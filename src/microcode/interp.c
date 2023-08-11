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
re_eval (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  stack_check (2, ic);
  stack_push (exp, ic);
  stack_push (env, ic);
  return INT_ACTION_EVAL;
}

static inline int_action_t
eval_subproblem (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  new_subproblem (exp, env, ic);
  return re_eval (exp, env, ic);
}

static inline int_action_t
eval_reduction (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  new_reduction (new_exp, env, ic);
  return re_eval (new_exp, env, ic);
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
  Free++ = proc;
  Free++ = env;
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
  Free++ = lambda;
  Free++ = env;
  return proc;
}

static inline SCHEME_OBJECT
make_extended_procedure (SCHEME_OBJECT lambda, SCHEME_OBJECT env)
{
  /* Deliberately omitted: EVAL_GC_CHECK (2); */
  SCHEME_OBJECT proc = (MAKE_POINTER_OBJECT (TC_EXTENDED_PROCEDURE, Free));
  Free++ = lambda;
  Free++ = env;
  return proc;
}

static inline int_action_t
eval_access (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  stack_check (CONTINUATION_SIZE, ic);
  push_cont_rc (RC_EXECUTE_ACCESS_FINISH, exp, ic);
  return eval_subproblem (access_environment (exp), env, ic);
}

static inline int_action_t
eval_assignment (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  stack_check (CONTINUATION_SIZE + 1, ic);
  stack_push (env, ic);
  push_cont_rc (RC_EXECUTE_ASSIGNMENT_FINISH, exp, ic);
  return eval_subproblem (assignment_value (exp), env, ic);
}

static inline int_action_t
eval_combination (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  unsigned long n_args = combination_size (exp) - 1;
  stack_check (CONTINUATION_SIZE + 2 + n_args, ic);
  decrement_sp (n_args, ic);
  stack_push (MAKE_OBJECT (TC_MANIFEST_NM_VECTOR, n_args), ic);
  if (n_args == 0)
    {
      stack_push (make_apply_frame_header (1), ic);
      push_cont_rc (RC_COMB_APPLY_FUNCTION, exp, ic);
    }
  else
    {
      stack_push (env);
      push_cont_rc (RC_COMB_SAVE_VALUE, exp, ic);
    }
  return eval_subproblem (combination_expr (exp, n_args), env, ic);
}

static inline int_action_t
eval_comment (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  return eval_reduction (comment_expression (exp), env, ic);
}

static inline int_action_t
eval_conditional (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  stack_check ((CONTINUATION_SIZE + 1), ic);
  push_cont_env (RC_CONDITIONAL_DECIDE, exp, env, ic);
  return eval_subproblem (conditional_predicate (exp), env, ic);
}

static inline int_action_t
eval_definition (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  stack_check ((CONTINUATION_SIZE + 1), ic);
  push_cont_env (RC_EXECUTE_DEFINITION_FINISH, exp, env, ic);
  return eval_subproblem (definition_value (exp), env, ic);
}

static inline int_action_t
eval_delay (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  return single_val (make_delayed (delay_object (exp), env), ic);
}

static inline int_action_t
eval_disjunction (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  stack_check (CONTINUATION_SIZE + 1, ic);
  push_cont_env (RC_DISJUNCTION_DECIDE, exp, env, ic);
  return eval_subproblem (disjunction_predicate (exp), env, ic);
}

static inline int_action_t
eval_extended_lambda (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  return single_val (make_extended_procedure (exp, env), ic);
}

static inline int_action_t
eval_lambda (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  return single_val (make_procedure (exp, env), ic);
}

static inline int_action_t
eval_scode_quote (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  return single_val (scode_quote_object (exp), ic);
}

static inline int_action_t
eval_sequence (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  stack_check ((CONTINUATION_SIZE + 1), ic);
  push_cont_env (RC_EXECUTE_SEQUENCE_FINISH, exp, env, ic);
  return eval_subproblem (sequence_1 (exp), env, ic);
}

static inline int_action_t
eval_variable (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  SCHEME_OBJECT val;
  long code = (lookup_variable (env, variable_name (exp), (&val)));
  if (code == PRIM_DONE)
    return single_val (val, ic);
  if ((VARIABLE_SAFE_P (exp)) && (code == ERR_UNASSIGNED_VARIABLE))
    return single_val (UNASSIGNED_OBJECT, ic);
  /* Back out of the evaluation. */
  if (code == PRIM_INTERRUPT)
    {
      PREPARE_EVAL_REPEAT ();
      SIGNAL_INTERRUPT (PENDING_INTERRUPTS ());
    }
  return eval_error (code);
}

static int_action_t
eval (SCHEME_OBJECT exp, SCHEME_OBJECT env, ptctx_t* ic)
{
  switch (OBJECT_TYPE (exp))
    {
    case TC_ACCESS:
      return eval_access (exp, env, ic);

    case TC_ASSIGNMENT:
      return eval_assignment (exp, env, ic);

    case TC_BROKEN_HEART:
      Microcode_Termination (TERM_BROKEN_HEART);

    case TC_COMBINATION:
      return eval_combination (exp, env, ic);

    case TC_COMMENT:
      return eval_comment (exp, env, ic);

#ifdef CC_SUPPORT_P
    case TC_COMPILED_ENTRY:
      dispatch_code = (enter_compiled_expression ());
      goto return_from_compiled_code;
#endif

    case TC_CONDITIONAL:
      return eval_conditional (exp, env, ic);

    case TC_DEFINITION:
      return eval_definition (exp, env, ic);

    case TC_DELAY:
      return eval_delay (exp, env, ic);

    case TC_DISJUNCTION:
      return eval_disjunction (exp, env, ic);

    case TC_EXTENDED_LAMBDA:
      return eval_extended_lambda (exp, env, ic);

    case TC_LAMBDA:
      return eval_lambda (exp, env, ic);

    case TC_MANIFEST_NM_VECTOR:
      return eval_error (ERR_EXECUTE_MANIFEST_VECTOR);

    case TC_SCODE_QUOTE:
      return eval_scode_quote (exp, env, ic);

    case TC_SEQUENCE:
      return eval_sequence (exp, env, ic);

    case TC_SYNTAX_ERROR:
      return eval_error (ERR_SYNTAX_ERROR);

    case TC_THE_ENVIRONMENT:
      return single_val (env, ic);

    case TC_VARIABLE:
      return eval_variable (exp, env, ic);

    default:
      return single_val (exp, ic);
    }
}

static inline int_action_t
cont_comb_apply_function (ptctx_t* ic)
{
  end_subproblem (ic);
  return INT_ACTION_APPLY_PROC;
}

static inline int_action_t
cont_comb_save_value (SCHEME_OBJECT exp, ptctx_t* ic)
{
  SCHEME_OBJECT env = stack_pop (ic);
  SCHEME_OBJECT val = get_single_val (ic);
  unsigned long arg = ((OBJECT_DATUM (stack_ref (0, ic))) - 1);
  stack_set (1 + arg, val, ic);
  stack_set (1, (MAKE_OBJECT (TC_MANIFEST_NM_VECTOR, arg)), ic);
  /* DO NOT count on the type code being NMVector here, since
     the stack parser may create them with #F! */
  if (arg > 0)
    push_cont_env (RC_COMB_SAVE_VALUE, exp, env, ic);
  else
    {
      stack_push (make_apply_frame_header (combination_size (exp)), ic);
      push_cont_rc (RC_COMB_APPLY_FUNCTION, exp, ic);
    }
  SCHEME_OBJECT new_exp = combination_expr (exp, arg);
  reuse_subproblem (new_exp, env, ic);
  return re_eval (new_exp, env, ic);
}

static inline int_action_t
cont_conditional_decide (SCHEME_OBJECT exp, ptctx_t* ic)
{
  end_subproblem (ic);
  SCHEME_OBJECT env = stack_pop (ic);
  SCHEME_OBJECT val = get_single_val (ic);
  SCHEME_OBJECT new_exp
    = ((val == SHARP_F)
       ? conditional_alternative (exp)
       : conditional_consequent (exp));
  return eval_reduction (new_exp, env, ic);
}

static inline int_action_t
cont_disjunction_decide (SCHEME_OBJECT exp, ptctx_t* ic)
{
  /* Return predicate if it isn't #F; else do ALTERNATIVE */
  end_subproblem (ic);
  SCHEME_OBJECT env = stack_pop (ic)
  SCHEME_OBJECT val = get_single_val (ic);
  if (val != SHARP_F)
    return single_val (val, ic);
  return eval_reduction (disjunction_alternative (exp), env, ic);
}

static inline int_action_t
cont_redo_evaluation (SCHEME_OBJECT exp, ptctx_t* ic)
{
  SCHEME_OBJECT env = stack_pop (ic);
  return eval_reduction (exp, env, ic);
}

static inline int_action_t
cont_access_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, ptctx_t* ic)
{
  SCHEME_OBJECT env = get_single_val (ic);
  SCHEME_OBJECT val;
  long code = (lookup_variable (env, access_name (exp), (&val)));
  switch (code)
    {
    case PRIM_DONE:
      end_subproblem (ic);
      return single_val (val, ic);

    case PRIM_INTERRUPT:
      PREPARE_POP_RETURN_INTERRUPT (RC_EXECUTE_ACCESS_FINISH, );
      SIGNAL_INTERRUPT (PENDING_INTERRUPTS ());
      return INT_ACTION_APPLY_PROC;

    default:
      push_cont (ret, exp);
      return eval_error (code);
    }
}

static inline int_action_t
cont_assignment_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, ptctx_t* ic)
{
  SCHEME_OBJECT env = stack_pop (ic);
  SCHEME_OBJECT val = get_single_val (ic);
  SCHEME_OBJECT variable = assignment_name (exp);
  SCHEME_OBJECT old_val;
  long code
    = (((OBJECT_TYPE (variable)) == TC_VARIABLE)
       ? (assign_variable (env, variable_name (variable), val, (&old_val)))
       : ERR_BAD_FRAME);
  if (code == PRIM_DONE)
    {
      end_subproblem (ic);
      return single_val (old_val, ic);
    }
  stack_push (env, ic);
  push_cont (ret, exp);
  if (code == PRIM_INTERRUPT)
    {
      push_cont_rc (RC_RESTORE_VALUE, val, ic);
      setup_interrupt (PENDING_INTERRUPTS ());
      return INT_ACTION_APPLY_PROC;
    }
  return eval_error (code);
}

static inline int_action_t
cont_definition_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, ptctx_t* ic)
{
  SCHEME_OBJECT env = stack_pop (ic);
  SCHEME_OBJECT val = get_single_val (ic);
  SCHEME_OBJECT name = definition_name (exp);
  long code = (define_variable (env, name, val));
  if (code == PRIM_DONE)
    {
      end_subproblem (ic);
      return single_val (name, ic);
    }
  stack_push (env, ic);
  push_cont (ret, exp, ic);
  if (code == PRIM_INTERRUPT)
    {
      push_cont_rc (RC_RESTORE_VALUE, val, ic);
      setup_interrupt (PENDING_INTERRUPTS ());
      return INT_ACTION_APPLY_PROC;
    }
  return eval_error (code);
}

static inline int_action_t
cont_hardware_trap (SCHEME_OBJECT ret, SCHEME_OBJECT exp, ptctx_t* ic)
{
  /* This just reinvokes the handler */
  SCHEME_OBJECT info = (stack_ref (0, ic));
  push_cont (ret, exp, ic);
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
  stack_check ((STACK_ENV_EXTRA_SLOTS + 2), ic);
  stack_push (info, ic);
  stack_push (handler, ic);
  stack_push ((make_apply_frame_header (2)), ic);
  return INT_ACTION_APPLY_PROC;
}

static inline int_action_t
cont_end_of_computation (ptctx_t* ic)
{
  /* Signals bottom of stack */
  interpreter_state_t* state = interpreter_state (ic);
  interpreter_state_t* previous_state = state->previous_state;
  if (previous_state != NULL_INTERPRETER_STATE)
    {
      set_dstack_position (state->dstack_position, ic);
      set_interpreter_state (previous_state, ic);
    }
  return INT_ACTION_DONE;
}

static inline int_action_t
cont_sequence_finish (SCHEME_OBJECT exp, ptctx_t* ic)
{
  end_subproblem (ic);
  SCHEME_OBJECT env = stack_pop (ic);
  return eval_reduction (sequence_2 (exp), env, ic);
}

static int_action_t
apply_cont (ptctx_t* ic)
{
  if (!RETURN_CODE_P (stack_ref (0, ic)))
    Microcode_Termination (TERM_BAD_STACK);

  SCHEME_OBJECT ret = stack_pop (ic);
  SCHEME_OBJECT exp = stack_pop (ic);
  switch (OBJECT_DATUM (ret))
    {
    case RC_COMB_APPLY_FUNCTION:
      return cont_comb_apply_function (ic);
    case RC_COMB_SAVE_VALUE:
      return cont_comb_save_value (exp, ic);
    case RC_CONDITIONAL_DECIDE:
      return cont_conditional_decide (exp, ic);
    case RC_DISJUNCTION_DECIDE:
      return cont_disjunction_decide (exp, ic);
    case RC_END_OF_COMPUTATION:
      return cont_end_of_computation (ic);
    case RC_EVAL_ERROR:
      return cont_redo_evaluation (exp, ic);
    case RC_EXECUTE_ACCESS_FINISH:
      return cont_access_finish (ret, exp, ic);
    case RC_EXECUTE_ASSIGNMENT_FINISH:
      return cont_assignment_finish (ret, exp, ic);
    case RC_EXECUTE_DEFINITION_FINISH:
      return cont_definition_finish (ret, exp, ic);
    case RC_HALT:
      Microcode_Termination (TERM_TERM_HANDLER);
    case RC_HARDWARE_TRAP:
      return cont_hardware_trap (ret, exp, ic);
    case RC_INTERNAL_APPLY:
      return INT_ACTION_APPLY_PROC;
    case RC_INTERNAL_APPLY_VAL:
      {
        stack_set (1, (get_single_val (ic)), ic);
        return INT_ACTION_APPLY_PROC;
      }

    case RC_JOIN_STACKLETS:
      unpack_control_point (exp, ic);
      return INT_ACTION_APPLY_CONT;

    case RC_NORMAL_GC_DONE:
      SET_VAL (GET_EXP);
      /* Paranoia */
      if (GC_NEEDED_P (gc_space_needed))
        termination_gc_out_of_space ();
      gc_space_needed = 0;
      EXIT_CRITICAL_SECTION ({ PUSH_CONT (GET_RET, GET_EXP); });
      break;

    case RC_POP_RETURN_ERROR:
    case RC_RESTORE_VALUE:
      return single_val (exp, ic);

    /* The following two return codes are both used to restore a
       saved history object.	The difference is that the first does
       not copy the history object while the second does.  In both
       cases, the GET_EXP contains the history object and the
       next item to be popped off the stack contains the offset back
       to the previous restore history return code.  */

    case RC_RESTORE_DONT_COPY_HISTORY:
      {
        increment_sp (1, ic);   // obsolete field
        set_history (OBJECT_ADDRESS (exp));
        set_prev_restore_history_offset (stack_pop (ic));
        return INT_ACTION_APPLY_CONT;
      }

    case RC_RESTORE_HISTORY:
      {
        if (!restore_history (exp, ic))
          {
            push_cont (ret, exp, ic);
            stack_check (CONTINUATION_SIZE, ic);
            push_cont_rc (RC_RESTORE_VALUE, get_single_val (ic));
            IMMEDIATE_GC (HEAP_AVAILABLE);
          }
        increment_sp (1, ic);   // obsolete field
        set_restore_history_offset_and_mark (stack_pop (ic), ic);
        return INT_ACTION_APPLY_CONT;
      }

    case RC_RESTORE_INT_MASK:
      SET_INTERRUPT_MASK (UNSIGNED_FIXNUM_TO_LONG (exp));
      if (GC_NEEDED_P (0))
        REQUEST_GC (0);
      if (PENDING_INTERRUPTS_P)
        {
          push_cont_rc (RC_RESTORE_VALUE, get_single_val (ic));
          SIGNAL_INTERRUPT (PENDING_INTERRUPTS ());
        }
      break;

    case RC_STACK_MARKER:
      /* Frame consists of the return code followed by two objects.
         The first object has already been popped into exp,
         so just pop the second argument.  */
      increment_sp (1, ic);
      break;

    case RC_EXECUTE_SEQUENCE_FINISH:
      return cont_sequence_finish (exp, ic);

    case RC_SNAP_NEED_THUNK:
      return single_value (snap_delayed (exp, get_single_val (ic)), ic);

#ifdef CC_SUPPORT_P
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

    default:
      POP_RETURN_ERROR (ERR_INAPPLICABLE_CONTINUATION);
    }
}

static int_action_t
apply_proc (ptctx_t* ic)
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

  if (PENDING_INTERRUPTS_P)
    {
      unsigned long interrupts = (PENDING_INTERRUPTS ());
      PREPARE_APPLY_INTERRUPT ();
      SIGNAL_INTERRUPT (interrupts);
    }

  {
    SCHEME_OBJECT proc = (apply_frame_proc ());
    switch (OBJECT_TYPE (proc))
      {
      case TC_ENTITY:
        {
          unsigned long frame_size = apply_frame_size (ic);
          SCHEME_OBJECT data = entity_data (proc);
          if (VECTOR_P (data) && (frame_size < VECTOR_LENGTH (data))
              && (VECTOR_REF (data, frame_size) != SHARP_F)
              && (VECTOR_REF (data, 0)
                  == VECTOR_REF (fixed_objects, ARITY_DISPATCHER_TAG)))
            set_apply_frame_proc (VECTOR_REF (data, frame_size), ic);
          else
            {
              increment_sp (1, ic); // discard header
              stack_push (entity_operator (proc), ic);
              stack_push (make_apply_frame_header (frame_size + 1), ic);
            }
          /* This must be done to prevent an infinite push loop by
             an entity whose handler is the entity itself or some
             other such loop.  Of course, it will die if stack overflow
             interrupts are disabled.  */
          stack_check (0, ic);
          return INT_ACTION_APPLY_PROC;
        }

      case TC_RECORD:
        {
          SCHEME_OBJECT applicator = record_applicator (proc);
          if (applicator == SHARP_F)
            APPLICATION_ERROR (ERR_INAPPLICABLE_OBJECT);
          unsigned long frame_size = apply_frame_size (ic);
          increment_sp (1, ic); // discard header
          stack_push (applicator, ic);
          stack_push (make_apply_frame_header (frame_size + 1));
          stack_check (0, ic);  // see above
          return INT_ACTION_APPLY_PROC;
        }

      case TC_PROCEDURE:
        {
          unsigned long frame_size = apply_frame_size (ic);
          SCHEME_OBJECT lambda = procedure_lambda (proc);
          {
            SCHEME_OBJECT names = lambda_names (lambda);
            if ((frame_size != VECTOR_LENGTH (names))
                && ((OBJECT_TYPE (lambda) != TC_LEXPR)
                    || (frame_size < VECTOR_LENGTH (names))))
              APPLICATION_ERROR (ERR_WRONG_NUMBER_OF_ARGUMENTS);
          }
          if (GC_NEEDED_P (frame_size + 1))
            {
              PREPARE_APPLY_INTERRUPT ();
              IMMEDIATE_GC (frame_size + 1);
            }
          SCHEME_OBJECT* end = Free + 1 + frame_size;
          SCHEME_OBJECT env = MAKE_POINTER_OBJECT (TC_ENVIRONMENT, Free);
          (*Free++) = MAKE_OBJECT (TC_MANIFEST_VECTOR, frame_size);
          increment_sp (1, ic); // discard header
          while (Free < end)
            (*Free++) = stack_pop (ic);
          return eval_reduction (lambda_body (lambda), env, ic);
        }

      case TC_CONTROL_POINT:
        if (apply_frame_size (ic) != 2)
          APPLICATION_ERROR (ERR_WRONG_NUMBER_OF_ARGUMENTS);
        SCHEME_OBJECT val = *(apply_frame_args (ic));
        unpack_control_point (proc, ic);
        reset_history (ic);
        return single_val (val, ic);

      case TC_PRIMITIVE:
        if (!IMPLEMENTED_PRIMITIVE_P (proc))
          APPLICATION_ERROR (ERR_UNIMPLEMENTED_PRIMITIVE);
        {
          unsigned long n_args = apply_frame_n_args (ic);
          if (PRIMITIVE_ARITY (proc) == LEXPR_PRIMITIVE_ARITY)
            set_primitive_lexpr_actuals (n_args, ic);
          else if (PRIMITIVE_ARITY (proc) != n_args)
            APPLICATION_ERROR (ERR_WRONG_NUMBER_OF_ARGUMENTS);

          // Primitives don't need header and proc:
          increment_sp (2, ic);
          // SET_EXP (proc);
          // APPLY_PRIMITIVE_FROM_INTERPRETER (proc);
          // POP_PRIMITIVE_FRAME (n_args);
          // goto pop_return;
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
          unsigned long nargs = apply_frame_n_args (ic);

          if ((nargs < reqs) || ((rest == 0) && (nargs > nfixed)))
            {
              APPLICATION_ERROR (ERR_WRONG_NUMBER_OF_ARGUMENTS);
            }

          unsigned long size = (/* proc: */ 1 + nparams + naux);
          unsigned long nwords
            = 1 /* vector header */
              + size
              /* rest list: */
              + ((nargs > nfixed) ? (2 * (nargs - nfixed)) : 0);
          if (GC_NEEDED_P (nwords))
            {
              PREPARE_APPLY_INTERRUPT ();
              IMMEDIATE_GC (nwords);
            }
          increment_sp (1, ic); // discard header
          SCHEME_OBJECT* scan = Free;
          SCHEME_OBJECT env = MAKE_POINTER_OBJECT (TC_ENVIRONMENT, scan);
          *scan++ = MAKE_OBJECT (TC_MANIFEST_VECTOR, size);
          if (nargs <= nfixed)
            {
              *scan++ = stack_pop (ic); // proc
              for (unsigned int i = 0; i < nargs; i += 1)
                *scan++ = stack_pop (ic);
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
              *scan++ = stack_pop (ic); // proc
              for (unsigned int i = 0; i < nfixed; i += 1)
                *scan++ = stack_pop (ic);
              *scan++ = list;
              for (unsigned int i = 0; i < naux; i += 1)
                *scan++ = UNASSIGNED_OBJECT;
              /* Now scan == OBJECT_ADDRESS (list) */
              for (unsigned int i = nfixed; i < nargs; i += 1)
                {
                  *scan++ = stack_pop (ic);
                  *scan = MAKE_POINTER_OBJECT (TC_LIST, scan + 1);
                  scan += 1;
                }
              scan[-1] = EMPTY_LIST;
            }
          Free = scan;
          return eval_reduction (elambda_body (lambda), env, ic);
        }

#ifdef CC_SUPPORT_P
      case TC_COMPILED_ENTRY:
        {
          guarantee_cc_return (1 + apply_frame_size (ic));
          long dispatch_code = apply_compiled_procedure ();
          switch (dispatch_code)
            {
            case PRIM_DONE:
              return single_val (???, ic);

            case PRIM_APPLY:
              return INT_ACTION_APPLY_PROC;

            case PRIM_INTERRUPT:
              SIGNAL_INTERRUPT (PENDING_INTERRUPTS ());

            case PRIM_APPLY_INTERRUPT:
              PREPARE_APPLY_INTERRUPT ();
              SIGNAL_INTERRUPT (PENDING_INTERRUPTS ());

            case ERR_INAPPLICABLE_OBJECT:
            case ERR_WRONG_NUMBER_OF_ARGUMENTS:
              APPLICATION_ERROR (dispatch_code);

            default:
              Do_Micro_Error (dispatch_code, true);
              return INT_ACTION_APPLY_PROC;
            }
        }
#endif

      default:
        APPLICATION_ERROR (ERR_INAPPLICABLE_OBJECT);
      }
  }
}
