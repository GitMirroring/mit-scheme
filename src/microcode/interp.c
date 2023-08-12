/* -*-C-*-

Copyright (C) 1986, 1987, 1988, 1989, 1990, 1991, 1992, 1993, 1994,
    1995, 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005,
    2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015, 2016,
    2017, 2018, 2019, 2020, 2021, 2022 Massachusetts Institute of
    Technology

This file is part of MIT/GNU Scheme.

MIT/GNU Scheme is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or (at
your option) any later version.

MIT/GNU Scheme is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with MIT/GNU Scheme; if not, write to the Free Software
Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301,
USA.

*/

#include "scheme.h"
#include "trap.h"
#include "lookup.h"
#include "history.h"

static inline int_action_t
re_eval (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check (2, tctx_stack (tctx));
  stack_push (exp, tctx_stack (tctx));
  stack_push (env, tctx_stack (tctx));
  return INT_ACTION_EVAL;
}

static inline int_action_t
eval_subproblem (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  new_subproblem (exp, env, tctx);
  return re_eval (exp, env, tctx);
}

static inline int_action_t
eval_reduction (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  new_reduction (exp, env, tctx);
  return re_eval (exp, env, tctx);
}

static inline int_action_t
eval_error (long code)
{
  Do_Micro_Error (code, false);
  return INT_ACTION_APPLY_PROC;
}

static inline SCHEME_OBJECT
make_delayed (SCHEME_OBJECT proc, SCHEME_OBJECT env)
{
  /* Deliberately omitted: EVAL_GC_CHECK (2); */
  SCHEME_OBJECT delayed = MAKE_POINTER_OBJECT (TC_DELAYED, Free);
  *Free++ = proc;
  *Free++ = env;
  return delayed;
}

static inline SCHEME_OBJECT
snap_delayed (SCHEME_OBJECT delayed, SCHEME_OBJECT val)
{
  // Don't snap thunk twice; evaluation of the thunk's body might have snapped
  // it already.
  if ((MEMORY_REF (delayed, 0)) == SHARP_T)
    return MEMORY_REF (delayed, 1);
  MEMORY_SET (delayed, 0, SHARP_T);
  MEMORY_SET (delayed, 1, val);
  return val;
}

static inline SCHEME_OBJECT
make_procedure (SCHEME_OBJECT lambda, SCHEME_OBJECT env)
{
  /* Deliberately omitted: EVAL_GC_CHECK (2); */
  SCHEME_OBJECT proc = (MAKE_POINTER_OBJECT (TC_PROCEDURE, Free));
  *Free++ = lambda;
  *Free++ = env;
  return proc;
}

static inline SCHEME_OBJECT
make_extended_procedure (SCHEME_OBJECT lambda, SCHEME_OBJECT env)
{
  /* Deliberately omitted: EVAL_GC_CHECK (2); */
  SCHEME_OBJECT proc = (MAKE_POINTER_OBJECT (TC_EXTENDED_PROCEDURE, Free));
  *Free++ = lambda;
  *Free++ = env;
  return proc;
}

static inline int_action_t
eval_access (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check (CONTINUATION_SIZE, tctx_stack (tctx));
  push_cont_env (RC_EXECUTE_ACCESS_FINISH, exp, env, tctx_stack (tctx));
  return eval_subproblem (access_environment (exp), env, tctx);
}

static inline int_action_t
eval_assignment (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check (CONTINUATION_SIZE + 1, tctx_stack (tctx));
  stack_push (env, tctx_stack (tctx));
  push_cont_rc (RC_EXECUTE_ASSIGNMENT_FINISH, exp, tctx_stack (tctx));
  return eval_subproblem (assignment_value (exp), env, tctx);
}

static inline int_action_t
eval_combination (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  unsigned long n_args = combination_size (exp) - 1;
  stack_check (CONTINUATION_SIZE + 2 + n_args, tctx_stack (tctx));
  decrement_sp (n_args, tctx_stack (tctx));
  stack_push (MAKE_OBJECT (TC_MANIFEST_NM_VECTOR, n_args), tctx_stack (tctx));
  if (n_args == 0)
    {
      stack_push (make_apply_frame_header (1), tctx_stack (tctx));
      push_cont_rc (RC_COMB_APPLY_FUNCTION, exp, tctx_stack (tctx));
    }
  else
    {
      stack_push (env, tctx_stack (tctx));
      push_cont_rc (RC_COMB_SAVE_VALUE, exp, tctx_stack (tctx));
    }
  return eval_subproblem (combination_expr (exp, n_args), env, tctx);
}

static inline int_action_t
eval_comment (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  return eval_reduction (comment_expression (exp), env, tctx);
}

static inline int_action_t
eval_conditional (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check ((CONTINUATION_SIZE + 1), tctx_stack (tctx));
  push_cont_env (RC_CONDITIONAL_DECIDE, exp, env, tctx_stack (tctx));
  return eval_subproblem (conditional_predicate (exp), env, tctx);
}

static inline int_action_t
eval_definition (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check ((CONTINUATION_SIZE + 1), tctx_stack (tctx));
  push_cont_env (RC_EXECUTE_DEFINITION_FINISH, exp, env, tctx_stack (tctx));
  return eval_subproblem (definition_value (exp), env, tctx);
}

static inline int_action_t
eval_delay (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  return single_val (make_delayed (delay_object (exp), env), tctx);
}

static inline int_action_t
eval_disjunction (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check (CONTINUATION_SIZE + 1, tctx_stack (tctx));
  push_cont_env (RC_DISJUNCTION_DECIDE, exp, env, tctx_stack (tctx));
  return eval_subproblem (disjunction_predicate (exp), env, tctx);
}

static inline int_action_t
eval_extended_lambda (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  return single_val (make_extended_procedure (exp, env), tctx);
}

static inline int_action_t
eval_lambda (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  return single_val (make_procedure (exp, env), tctx);
}

static inline int_action_t
eval_scode_quote (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  return single_val (scode_quote_object (exp), tctx);
}

static inline int_action_t
eval_sequence (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check ((CONTINUATION_SIZE + 1), tctx_stack (tctx));
  push_cont_env (RC_EXECUTE_SEQUENCE_FINISH, exp, env, tctx_stack (tctx));
  return eval_subproblem (sequence_1 (exp), env, tctx);
}

static inline int_action_t
eval_variable (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  SCHEME_OBJECT val;
  long code = (lookup_variable (env, variable_name (exp), (&val)));
  if (code == PRIM_DONE)
    return single_val (val, tctx);
  if (variable_safe_p (exp) && (code == ERR_UNASSIGNED_VARIABLE))
    return single_val (UNASSIGNED_OBJECT, tctx);
  /* Back out of the evaluation. */
  if (code == PRIM_INTERRUPT)
    {
      sstack_t* s = tctx_stack (tctx);
      stack_check (CONTINUATION_SIZE + 1, s);
      push_cont_env (RC_EVAL_ERROR, exp, env, s);
      setup_interrupt (PENDING_INTERRUPTS (), tctx);
      return INT_ACTION_APPLY_PROC;
    }
  return eval_error (code);
}

static int_action_t
eval (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  switch (OBJECT_TYPE (exp))
    {
    case TC_ACCESS:
      return eval_access (exp, env, tctx);

    case TC_ASSIGNMENT:
      return eval_assignment (exp, env, tctx);

    case TC_BROKEN_HEART:
      Microcode_Termination (TERM_BROKEN_HEART);

    case TC_COMBINATION:
      return eval_combination (exp, env, tctx);

    case TC_COMMENT:
      return eval_comment (exp, env, tctx);

#ifdef CC_SUPPORT_P
#if 0
    case TC_COMPILED_ENTRY:
      dispatch_code = (enter_compiled_expression ());
      goto return_from_compiled_code;
#endif
#endif

    case TC_CONDITIONAL:
      return eval_conditional (exp, env, tctx);

    case TC_DEFINITION:
      return eval_definition (exp, env, tctx);

    case TC_DELAY:
      return eval_delay (exp, env, tctx);

    case TC_DISJUNCTION:
      return eval_disjunction (exp, env, tctx);

    case TC_EXTENDED_LAMBDA:
      return eval_extended_lambda (exp, env, tctx);

    case TC_LAMBDA:
      return eval_lambda (exp, env, tctx);

    case TC_MANIFEST_NM_VECTOR:
      return eval_error (ERR_EXECUTE_MANIFEST_VECTOR);

    case TC_SCODE_QUOTE:
      return eval_scode_quote (exp, env, tctx);

    case TC_SEQUENCE:
      return eval_sequence (exp, env, tctx);

    case TC_SYNTAX_ERROR:
      return eval_error (ERR_SYNTAX_ERROR);

    case TC_THE_ENVIRONMENT:
      return single_val (env, tctx);

    case TC_VARIABLE:
      return eval_variable (exp, env, tctx);

    default:
      return single_val (exp, tctx);
    }
}

static inline int_action_t
cont_comb_apply_function (tctx_t* tctx)
{
  end_subproblem (tctx);
  return INT_ACTION_APPLY_PROC;
}

static inline int_action_t
cont_comb_save_value (SCHEME_OBJECT exp, tctx_t* tctx)
{
  SCHEME_OBJECT env = stack_pop (tctx_stack (tctx));
  SCHEME_OBJECT val = get_single_val (tctx);
  unsigned long arg = ((OBJECT_DATUM (stack_ref (0, tctx_stack (tctx)))) - 1);
  stack_set (1 + arg, val, tctx_stack (tctx));
  stack_set (1, (MAKE_OBJECT (TC_MANIFEST_NM_VECTOR, arg)), tctx_stack (tctx));
  /* DO NOT count on the type code being NMVector here, since
     the stack parser may create them with #F! */
  if (arg > 0)
    push_cont_env (RC_COMB_SAVE_VALUE, exp, env, tctx_stack (tctx));
  else
    {
      stack_push (make_apply_frame_header (combination_size (exp)),
                  tctx_stack (tctx));
      push_cont_rc (RC_COMB_APPLY_FUNCTION, exp, tctx_stack (tctx));
    }
  SCHEME_OBJECT new_exp = combination_expr (exp, arg);
  reuse_subproblem (new_exp, env, tctx);
  return re_eval (new_exp, env, tctx);
}

static inline int_action_t
cont_conditional_decide (SCHEME_OBJECT exp, tctx_t* tctx)
{
  end_subproblem (tctx);
  SCHEME_OBJECT env = stack_pop (tctx_stack (tctx));
  SCHEME_OBJECT val = get_single_val (tctx);
  SCHEME_OBJECT new_exp
    = ((val == SHARP_F)
       ? conditional_alternative (exp)
       : conditional_consequent (exp));
  return eval_reduction (new_exp, env, tctx);
}

static inline int_action_t
cont_disjunction_decide (SCHEME_OBJECT exp, tctx_t* tctx)
{
  /* Return predicate if it isn't #F; else do ALTERNATIVE */
  end_subproblem (tctx);
  SCHEME_OBJECT env = stack_pop (tctx_stack (tctx));
  SCHEME_OBJECT val = get_single_val (tctx);
  if (val != SHARP_F)
    return single_val (val, tctx);
  return eval_reduction (disjunction_alternative (exp), env, tctx);
}

static inline int_action_t
cont_redo_evaluation (SCHEME_OBJECT exp, tctx_t* tctx)
{
  SCHEME_OBJECT env = stack_pop (tctx_stack (tctx));
  return eval_reduction (exp, env, tctx);
}

static inline int_action_t
cont_access_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, tctx_t* tctx)
{
  SCHEME_OBJECT env = stack_pop (tctx_stack (tctx));
  sstack_t* s = tctx_stack (tctx);
  SCHEME_OBJECT val;
  long code = (lookup_variable (env, access_name (exp), (&val)));
  switch (code)
    {
    case PRIM_DONE:
      end_subproblem (tctx);
      return single_val (val, tctx);

    case PRIM_INTERRUPT:
      push_cont_rc (RC_EXECUTE_ACCESS_FINISH, exp, s);
      push_cont_rc (RC_RESTORE_VALUE, get_single_val (tctx), s);
      setup_interrupt (PENDING_INTERRUPTS (), tctx);
      return INT_ACTION_APPLY_PROC;

    default:
      push_cont (ret, exp, s);
      return eval_error (code);
    }
}

static inline int_action_t
cont_assignment_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, tctx_t* tctx)
{
  SCHEME_OBJECT env = stack_pop (tctx_stack (tctx));
  SCHEME_OBJECT val = get_single_val (tctx);
  SCHEME_OBJECT variable = assignment_name (exp);
  SCHEME_OBJECT old_val;
  long code
    = (((OBJECT_TYPE (variable)) == TC_VARIABLE)
       ? (assign_variable (env, variable_name (variable), val, (&old_val)))
       : ERR_BAD_FRAME);
  if (code == PRIM_DONE)
    {
      end_subproblem (tctx);
      return single_val (old_val, tctx);
    }
  stack_push (env, tctx_stack (tctx));
  push_cont (ret, exp, tctx_stack (tctx));
  if (code == PRIM_INTERRUPT)
    {
      push_cont_rc (RC_RESTORE_VALUE, val, tctx_stack (tctx));
      setup_interrupt (PENDING_INTERRUPTS (), tctx);
      return INT_ACTION_APPLY_PROC;
    }
  return eval_error (code);
}

static inline int_action_t
cont_definition_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, tctx_t* tctx)
{
  SCHEME_OBJECT env = stack_pop (tctx_stack (tctx));
  SCHEME_OBJECT val = get_single_val (tctx);
  SCHEME_OBJECT name = definition_name (exp);
  long code = (define_variable (env, name, val));
  if (code == PRIM_DONE)
    {
      end_subproblem (tctx);
      return single_val (name, tctx);
    }
  stack_push (env, tctx_stack (tctx));
  push_cont (ret, exp, tctx_stack (tctx));
  if (code == PRIM_INTERRUPT)
    {
      push_cont_rc (RC_RESTORE_VALUE, val, tctx_stack (tctx));
      setup_interrupt (PENDING_INTERRUPTS (), tctx);
      return INT_ACTION_APPLY_PROC;
    }
  return eval_error (code);
}

static inline int_action_t
cont_hardware_trap (SCHEME_OBJECT ret, SCHEME_OBJECT exp, tctx_t* tctx)
{
  /* This just reinvokes the handler */
  SCHEME_OBJECT info = (stack_ref (0, tctx_stack (tctx)));
  push_cont (ret, exp, tctx_stack (tctx));
  SCHEME_OBJECT handler
    = ((VECTOR_P (fixed_objects))
       ? (VECTOR_REF (fixed_objects, TRAP_HANDLER))
       : SHARP_F);
  if (handler == SHARP_F)
    {
      outf_fatal ("There is no trap handler for recovery!\n");
      termination_trap ();
      /*NOTREACHED*/
    }
  stack_check ((STACK_ENV_EXTRA_SLOTS + 2), tctx_stack (tctx));
  stack_push (info, tctx_stack (tctx));
  stack_push (handler, tctx_stack (tctx));
  stack_push ((make_apply_frame_header (2)), tctx_stack (tctx));
  return INT_ACTION_APPLY_PROC;
}

static inline int_action_t
cont_end_of_computation (tctx_t* tctx)
{
  /* Signals bottom of stack */
  interpreter_state_t* state = interpreter_state (tctx);
  interpreter_state_t* previous_state = state->previous_state;
  if (previous_state != NULL_INTERPRETER_STATE)
    {
      dstack_set_position (state->dstack_position);
      set_interpreter_state (previous_state, tctx);
    }
  return INT_ACTION_DONE;
}

static inline int_action_t
cont_sequence_finish (SCHEME_OBJECT exp, tctx_t* tctx)
{
  end_subproblem (tctx);
  SCHEME_OBJECT env = stack_pop (tctx_stack (tctx));
  return eval_reduction (sequence_2 (exp), env, tctx);
}

static int_action_t
apply_cont (tctx_t* tctx)
{
  sstack_t* s = tctx_stack (tctx);
  if (!RETURN_CODE_P (stack_ref (0, s)))
    Microcode_Termination (TERM_BAD_STACK);

  SCHEME_OBJECT ret = stack_pop (s);
  SCHEME_OBJECT exp = stack_pop (s);
  switch (OBJECT_DATUM (ret))
    {
    case RC_COMB_APPLY_FUNCTION:
      return cont_comb_apply_function (tctx);
    case RC_COMB_SAVE_VALUE:
      return cont_comb_save_value (exp, tctx);
    case RC_CONDITIONAL_DECIDE:
      return cont_conditional_decide (exp, tctx);
    case RC_DISJUNCTION_DECIDE:
      return cont_disjunction_decide (exp, tctx);
    case RC_END_OF_COMPUTATION:
      return cont_end_of_computation (tctx);
    case RC_EVAL_ERROR:
      return cont_redo_evaluation (exp, tctx);
    case RC_EXECUTE_ACCESS_FINISH:
      return cont_access_finish (ret, exp, tctx);
    case RC_EXECUTE_ASSIGNMENT_FINISH:
      return cont_assignment_finish (ret, exp, tctx);
    case RC_EXECUTE_DEFINITION_FINISH:
      return cont_definition_finish (ret, exp, tctx);
    case RC_HALT:
      Microcode_Termination (TERM_TERM_HANDLER);
    case RC_HARDWARE_TRAP:
      return cont_hardware_trap (ret, exp, tctx);
    case RC_INTERNAL_APPLY:
      return INT_ACTION_APPLY_PROC;
    case RC_INTERNAL_APPLY_VAL:
      {
        stack_set (1, (get_single_val (tctx)), s);
        return INT_ACTION_APPLY_PROC;
      }

    case RC_JOIN_STACKLETS:
      unpack_control_point (exp, s);
      return INT_ACTION_APPLY_CONT;

    case RC_NORMAL_GC_DONE:
      /* Paranoia */
      if (GC_NEEDED_P (gc_space_needed))
        termination_gc_out_of_space ();
      gc_space_needed = 0;
      EXIT_CRITICAL_SECTION ({ push_cont (ret, exp, s); });
      return single_val (exp, tctx);

    case RC_POP_RETURN_ERROR:
    case RC_RESTORE_VALUE:
      return single_val (exp, tctx);

    /* The following two return codes are both used to restore a
       saved history object.	The difference is that the first does
       not copy the history object while the second does.  In both
       cases, the GET_EXP contains the history object and the
       next item to be popped off the stack contains the offset back
       to the previous restore history return code.  */

    case RC_RESTORE_DONT_COPY_HISTORY:
      increment_sp (1, s);    // obsolete field
      set_history (exp, tctx);
      set_restore_history_offset (stack_pop (s), tctx);
      return INT_ACTION_APPLY_CONT;

    case RC_RESTORE_HISTORY:
      if (!restore_history (exp, tctx))
        {
          push_cont (ret, exp, s);
          stack_check (CONTINUATION_SIZE, s);
          push_cont_rc (RC_RESTORE_VALUE, get_single_val (tctx), s);
          REQUEST_GC (HEAP_AVAILABLE);
          setup_interrupt (PENDING_INTERRUPTS (), tctx);
          return INT_ACTION_APPLY_PROC;
        }
      increment_sp (1, s); // obsolete field
      set_restore_history_offset_and_mark (stack_pop (s), tctx);
      return INT_ACTION_APPLY_CONT;

    case RC_RESTORE_INT_MASK:
      SET_INTERRUPT_MASK (UNSIGNED_FIXNUM_TO_LONG (exp));
      if (GC_NEEDED_P (0))
        REQUEST_GC (0);
      if (PENDING_INTERRUPTS_P)
        {
          push_cont_rc (RC_RESTORE_VALUE, get_single_val (tctx), s);
          setup_interrupt (PENDING_INTERRUPTS (), tctx);
          return INT_ACTION_APPLY_PROC;
        }
      return INT_ACTION_APPLY_CONT;

    case RC_STACK_MARKER:
      /* Frame consists of the return code followed by two objects.
         The first object has already been popped into exp,
         so just pop the second argument.  */
      increment_sp (1, s);
      return INT_ACTION_APPLY_CONT;

    case RC_EXECUTE_SEQUENCE_FINISH:
      return cont_sequence_finish (exp, tctx);

    case RC_SNAP_NEED_THUNK:
      return single_val (snap_delayed (exp, get_single_val (tctx)), tctx);

#ifdef CC_SUPPORT_P
#if 0
#define CREST(return_code, entry)                                       \
    case return_code:                                                   \
      {                                                                 \
        dispatch_code = (entry ());                                     \
        goto return_from_compiled_code;                                 \
      }
      CREST (RC_COMP_INTERRUPT_RESTART, comp_interrupt_restart);
      CREST (RC_COMP_LOOKUP_TRAP_RESTART, comp_lookup_trap_restart);
      CREST (RC_COMP_ASSIGNMENT_TRAP_RESTART, comp_assignment_trap_restart);
      CREST (RC_COMP_OP_REF_TRAP_RESTART, comp_op_lookup_trap_restart);
      CREST (RC_COMP_CACHE_REF_APPLY_RESTART, comp_cache_lookup_apply_restart);
      CREST (RC_COMP_SAFE_REF_TRAP_RESTART, comp_safe_lookup_trap_restart);
      CREST (RC_COMP_UNASSIGNED_TRAP_RESTART, comp_unassigned_p_trap_restart);
      CREST (RC_COMP_LINK_CACHES_RESTART, comp_link_caches_restart);
      CREST (RC_COMP_ERROR_RESTART, comp_error_restart);

    case RC_REENTER_COMPILED_CODE:
      dispatch_code = return_to_compiled_code ();
      return INT_ACTION_RETURN_FROM_COMPILED_CODE;
#endif
#endif

    default:
      push_cont (ret, exp, s);
      Do_Micro_Error (ERR_INAPPLICABLE_CONTINUATION, true);
      return INT_ACTION_APPLY_PROC;
    }
}

static int_action_t
apply_proc (tctx_t* tctx)
{
  /* internal_apply, the core of the application mechanism.

       Branch here to perform a function application.

       At this point the top of the stack contains an application
       frame which consists of the following elements (see sdata.h):

       - A header specifying the frame length.
       - A procedure.
       - The actual (evaluated) arguments.

       No registers (except the stack pointer) are meaningful at
       this point.  Before interrupts or errors are processed, some
       registers are cleared to avoid holding onto garbage if a
       garbage collection occurs.  */

  sstack_t* s = tctx_stack (tctx);
  if (PENDING_INTERRUPTS_P)
    {
      unsigned long interrupts = (PENDING_INTERRUPTS ());
      push_cont_rc (RC_INTERNAL_APPLY_VAL, apply_frame_proc (s), s);
      setup_interrupt (interrupts, tctx);
      return INT_ACTION_APPLY_PROC;
    }

  SCHEME_OBJECT proc = (apply_frame_proc (s));
  switch (OBJECT_TYPE (proc))
    {
    case TC_ENTITY:
      {
        unsigned long frame_size = apply_frame_size (s);
        SCHEME_OBJECT data = entity_data (proc);
        if (VECTOR_P (data) && (frame_size < VECTOR_LENGTH (data))
            && (VECTOR_REF (data, frame_size) != SHARP_F)
            && (VECTOR_REF (data, 0)
                == VECTOR_REF (fixed_objects, ARITY_DISPATCHER_TAG)))
          set_apply_frame_proc (VECTOR_REF (data, frame_size), s);
        else
          {
            increment_sp (1, s); // discard header
            stack_push (entity_operator (proc), s);
            stack_push (make_apply_frame_header (frame_size + 1), s);
          }
        /* This must be done to prevent an infinite push loop by
           an entity whose handler is the entity itself or some
           other such loop.  Of course, it will die if stack overflow
           interrupts are disabled.  */
        stack_check (0, s);
        return INT_ACTION_APPLY_PROC;
      }

    case TC_RECORD:
      {
        SCHEME_OBJECT applicator = record_applicator (proc);
        if (applicator == SHARP_F)
          {
            push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
            Do_Micro_Error (ERR_INAPPLICABLE_OBJECT, true);
            return INT_ACTION_APPLY_PROC;
          }
        unsigned long frame_size = apply_frame_size (s);
        increment_sp (1, s); // discard header
        stack_push (applicator, s);
        stack_push (make_apply_frame_header (frame_size + 1), s);
        stack_check (0, s); // see above
        return INT_ACTION_APPLY_PROC;
      }

    case TC_PROCEDURE:
      {
        unsigned long frame_size = apply_frame_size (s);
        SCHEME_OBJECT lambda = procedure_lambda (proc);
        {
          SCHEME_OBJECT names = lambda_names (lambda);
          if ((frame_size != VECTOR_LENGTH (names))
              && ((OBJECT_TYPE (lambda) != TC_LEXPR)
                  || (frame_size < VECTOR_LENGTH (names))))
            {
              push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
              Do_Micro_Error (ERR_WRONG_NUMBER_OF_ARGUMENTS, true);
              return INT_ACTION_APPLY_PROC;
            }
        }
        if (GC_NEEDED_P (frame_size + 1))
          {
            push_cont_rc (RC_INTERNAL_APPLY_VAL, apply_frame_proc (s), s);
            REQUEST_GC (frame_size + 1);
            setup_interrupt (PENDING_INTERRUPTS (), tctx);
            return INT_ACTION_APPLY_PROC;
          }
        SCHEME_OBJECT* end = Free + 1 + frame_size;
        SCHEME_OBJECT env = MAKE_POINTER_OBJECT (TC_ENVIRONMENT, Free);
        (*Free++) = MAKE_OBJECT (TC_MANIFEST_VECTOR, frame_size);
        increment_sp (1, s); // discard header
        while (Free < end)
          (*Free++) = stack_pop (s);
        return eval_reduction (lambda_body (lambda), env, tctx);
      }

    case TC_CONTROL_POINT:
      if (apply_frame_size (s) != 2)
        {
          push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
          Do_Micro_Error (ERR_WRONG_NUMBER_OF_ARGUMENTS, true);
          return INT_ACTION_APPLY_PROC;
        }
      SCHEME_OBJECT val = apply_frame_first_arg (s);
      unpack_control_point (proc, s);
      reset_history (tctx);
      return single_val (val, tctx);

    case TC_PRIMITIVE:
      if (!IMPLEMENTED_PRIMITIVE_P (proc))
        {
          push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
          Do_Micro_Error (ERR_UNIMPLEMENTED_PRIMITIVE, true);
          return INT_ACTION_APPLY_PROC;
        }
      {
        unsigned long n_args = apply_frame_n_args (s);
        if (PRIMITIVE_ARITY (proc) == LEXPR_PRIMITIVE_ARITY)
          set_primitive_lexpr_actuals (n_args, tctx);
        else if (PRIMITIVE_ARITY (proc) != n_args)
          {
            push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
            Do_Micro_Error (ERR_WRONG_NUMBER_OF_ARGUMENTS, true);
            return INT_ACTION_APPLY_PROC;
          }

        // Primitives don't need header and proc:
        increment_sp (2, s);
        primitive_apply_internal (proc, tctx);
        increment_sp (n_args, s);
        return INT_ACTION_APPLY_CONT;
      }

    case TC_EXTENDED_PROCEDURE:
      {
        SCHEME_OBJECT lambda = procedure_lambda (proc);
        unsigned long nnames = VECTOR_LENGTH (elambda_names (lambda));
        unsigned long reqs = elambda_reqs (lambda);
        unsigned long opts = elambda_opts (lambda);
        unsigned long rest = elambda_rest (lambda);
        unsigned long nfixed = reqs + opts;
        unsigned long nparams = nfixed + rest;
        unsigned long naux = nnames - nparams;
        unsigned long nargs = apply_frame_n_args (s);

        if ((nargs < reqs) || ((rest == 0) && (nargs > nfixed)))
          {
            push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
            Do_Micro_Error (ERR_WRONG_NUMBER_OF_ARGUMENTS, true);
            return INT_ACTION_APPLY_PROC;
          }

        unsigned long size = (/* proc: */ 1 + nparams + naux);
        unsigned long nwords
          = 1 /* vector header */
            + size
            /* rest list: */
            + ((nargs > nfixed) ? (2 * (nargs - nfixed)) : 0);
        if (GC_NEEDED_P (nwords))
          {
            push_cont_rc (RC_INTERNAL_APPLY_VAL, apply_frame_proc (s), s);
            REQUEST_GC (nwords);
            setup_interrupt (PENDING_INTERRUPTS (), tctx);
            return INT_ACTION_APPLY_PROC;
          }
        increment_sp (1, s); // discard header
        SCHEME_OBJECT* scan = Free;
        SCHEME_OBJECT env = MAKE_POINTER_OBJECT (TC_ENVIRONMENT, scan);
        *scan++ = MAKE_OBJECT (TC_MANIFEST_VECTOR, size);
        if (nargs <= nfixed)
          {
            *scan++ = stack_pop (s); // proc
            for (unsigned int i = 0; i < nargs; i += 1)
              *scan++ = stack_pop (s);
            for (unsigned int i = nargs; i < nfixed; i += 1)
              *scan++ = DEFAULT_OBJECT;
            if (rest == 1)
              *scan++ = EMPTY_LIST;
            for (unsigned int i = 0; i < naux; i += 1)
              *scan++ = UNASSIGNED_OBJECT;
          }
        else
          {
            /* assert (rest == 1) */
            SCHEME_OBJECT list = MAKE_POINTER_OBJECT (TC_LIST, scan + size);
            *scan++ = stack_pop (s); // proc
            for (unsigned int i = 0; i < nfixed; i += 1)
              *scan++ = stack_pop (s);
            *scan++ = list;
            for (unsigned int i = 0; i < naux; i += 1)
              *scan++ = UNASSIGNED_OBJECT;
            /* Now scan == OBJECT_ADDRESS (list) */
            for (unsigned int i = nfixed; i < nargs; i += 1)
              {
                *scan++ = stack_pop (s);
                *scan = MAKE_POINTER_OBJECT (TC_LIST, scan + 1);
                scan += 1;
              }
            scan[-1] = EMPTY_LIST;
          }
        Free = scan;
        return eval_reduction (elambda_body (lambda), env, tctx);
      }

#ifdef CC_SUPPORT_P
    case TC_COMPILED_ENTRY:
      {
        guarantee_cc_return (1 + apply_frame_size (s));
        long dispatch_code = apply_compiled_procedure ();
        switch (dispatch_code)
          {
          case PRIM_DONE:
            return single_val (GET_CC_VAL, tctx);

          case PRIM_APPLY:
            return INT_ACTION_APPLY_PROC;

          case PRIM_INTERRUPT:
            setup_interrupt (PENDING_INTERRUPTS (), tctx);
            return INT_ACTION_APPLY_PROC;

          case PRIM_APPLY_INTERRUPT:
            push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
            setup_interrupt (PENDING_INTERRUPTS (), tctx);
            return INT_ACTION_APPLY_PROC;

          case ERR_INAPPLICABLE_OBJECT:
          case ERR_WRONG_NUMBER_OF_ARGUMENTS:
            push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
            Do_Micro_Error (dispatch_code, true);
            return INT_ACTION_APPLY_PROC;

          default:
            Do_Micro_Error (dispatch_code, true);
            return INT_ACTION_APPLY_PROC;
          }
      }
#endif

    default:
      push_cont_rc (RC_INTERNAL_APPLY_VAL, SHARP_F, s);
      Do_Micro_Error (ERR_INAPPLICABLE_OBJECT, true);
      return INT_ACTION_APPLY_PROC;
    }
}

void
interpreter (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  int_action_t action = eval (exp, env, tctx);
  while (true)
    switch (action)
      {
      case INT_ACTION_APPLY_CONT:
        action = apply_cont (tctx);
        break;

      case INT_ACTION_APPLY_PROC:
        action = apply_proc (tctx);
        break;

      case INT_ACTION_EVAL:
        SCHEME_OBJECT exp2 = get_val (0, tctx);
        SCHEME_OBJECT env2 = get_val (1, tctx);
        reset_vals (tctx);
        action = eval (exp2, env2, tctx);
        break;

      case INT_ACTION_RETURN_FROM_COMPILED_CODE:
        // ??????
        break;

      case INT_ACTION_DONE:
        return;
      }
}
