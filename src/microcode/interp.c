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

ictx_t*
new_ictx (unsigned long size, SCHEME_OBJECT* block)
{
  ictx_t* ic = (malloc (sizeof (ictx_t)));
  if (ic == 0)
    {
      outf_fatal ("\n%s: unable to allocate ictx_t\n",
		  scheme_program_name);
      Microcode_Termination (TERM_EXIT);
    }
  ic->stack_start = block;
  ic->stack_guard = (block + STACK_GUARD_SIZE);
  ic->stack_end = (block + size);
  ic->stack_pointer = ic->end;
  (*block) = (MAKE_BROKEN_HEART (block));
  ic->value_pointer = ic->value_store;
  ic->history
    = (((VECTOR_P (fixed_objects))
	&& ((READ_DUMMY_HISTORY ()) != SHARP_F))
       ? (OBJECT_ADDRESS (READ_DUMMY_HISTORY ()))
       : (make_dummy_history ()));
  return ic;
}

static inline int_action_t
re_eval (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  stack_check (2, ic);
  stack_push (exp, ic);
  stack_push (env, ic);
  return INT_ACTION_EVAL;
}

static inline int_action_t
eval_subproblem (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  new_subproblem (exp, env, ic);
  return re_eval (exp, env, ic);
}

static inline int_action_t
eval_reduction (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
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

static inline int_action_t
eval_access (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  stack_check (CONTINUATION_SIZE, ic);
  push_cont_rc (RC_EXECUTE_ACCESS_FINISH, exp, ic);
  return eval_subproblem (access_environment (exp), env, ic);
}

static inline int_action_t
eval_assignment (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  stack_check ((CONTINUATION_SIZE + 1), ic);
  stack_push (env, ic);
  push_cont_rc (RC_EXECUTE_ASSIGNMENT_FINISH, exp, ic);
  return eval_subproblem (assignment_value (exp), env, ic);
}

static inline int_action_t
eval_combination (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  unsigned long n_args = (combination_size (exp) - 1);
  stack_check ((CONTINUATION_SIZE + 2 + n_args), ic);
  decrement_sp (n_args, ic);
  stack_push ((MAKE_OBJECT (TC_MANIFEST_NM_VECTOR, n_args)), ic);
  if (n_args == 0)
    {
      stack_push (make_apply_frame_header (0), ic);
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
eval_comment (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  return eval_reduction (comment_expression (exp), env, ic);
}

static inline int_action_t
eval_conditional (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  stack_check ((CONTINUATION_SIZE + 1), ic);
  push_cont_env (RC_CONDITIONAL_DECIDE, exp, env, ic);
  return eval_subproblem (conditional_predicate (exp), env, ic);
}

static inline int_action_t
eval_definition (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  stack_check ((CONTINUATION_SIZE + 1), ic);
  push_cont_env (RC_EXECUTE_DEFINITION_FINISH, exp, env, ic);
  return eval_subproblem (definition_value (exp), env, ic);
}

static inline int_action_t
eval_delay (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  /* Deliberately omitted: EVAL_GC_CHECK (2); */
  SCHEME_OBJECT delayed = (MAKE_POINTER_OBJECT (TC_DELAYED, Free));
  (Free[THUNK_ENVIRONMENT]) = env;
  (Free[THUNK_PROCEDURE]) = delay_object (exp);
  Free += 2;
  return single_val (delayed, ic);
}

static inline int_action_t
eval_disjunction (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  stack_check ((CONTINUATION_SIZE + 1), ic);
  push_cont_env (RC_DISJUNCTION_DECIDE, exp, env, ic);
  return eval_subproblem (disjunction_predicate (exp), env, ic);
}

static inline int_action_t
eval_extended_lambda (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  /* Deliberately omitted: EVAL_GC_CHECK (2); */
  SCHEME_OBJECT proc = (MAKE_POINTER_OBJECT (TC_EXTENDED_PROCEDURE, Free));
  (Free[PROCEDURE_LAMBDA_EXPR]) = exp;
  (Free[PROCEDURE_ENVIRONMENT]) = env;
  Free += 2;
  return single_val (proc, ic);
}

static inline int_action_t
eval_lambda (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  /* Deliberately omitted: EVAL_GC_CHECK (2); */
  SCHEME_OBJECT proc = (MAKE_POINTER_OBJECT (TC_PROCEDURE, Free));
  (Free[PROCEDURE_LAMBDA_EXPR]) = exp;
  (Free[PROCEDURE_ENVIRONMENT]) = env;
  Free += 2;
  return single_val (proc, ic);
}

static inline int_action_t
eval_scode_quote (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  return single_val (scode_quote_object (exp), ic);
}

static inline int_action_t
eval_sequence (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
{
  stack_check ((CONTINUATION_SIZE + 1), ic);
  push_cont_env (RC_EXECUTE_SEQUENCE_FINISH, exp, env, ic);
  return eval_subproblem (sequence_1 (exp), env, ic);
}

static inline int_action_t
eval_variable (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
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
eval (SCHEME_OBJECT exp, SCHEME_OBJECT env, ictx_t* ic)
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
cont_comb_apply_function (ictx_t* ic)
{
  end_subproblem (ic);
  return INT_ACTION_APPLY_PROC;
}

static inline int_action_t
cont_comb_save_value (SCHEME_OBJECT exp, ictx_t* ic)
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
cont_conditional_decide (SCHEME_OBJECT exp, ictx_t* ic)
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
cont_disjunction_decide (SCHEME_OBJECT exp, ictx_t* ic)
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
cont_redo_evaluation (SCHEME_OBJECT exp, ictx_t* ic)
{
  SCHEME_OBJECT env = stack_pop (ic);
  return eval_reduction (exp, env, ic);
}

static inline int_action_t
cont_access_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, ictx_t* ic)
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
cont_assignment_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, ictx_t* ic)
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
cont_definition_finish (SCHEME_OBJECT ret, SCHEME_OBJECT exp, ictx_t* ic)
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
cont_hardware_trap (SCHEME_OBJECT ret, SCHEME_OBJECT exp, ictx_t* ic)
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
  stack_push ((make_apply_frame_header (1)), ic);
  return INT_ACTION_APPLY_PROC;
}

static inline int_action_t
cont_end_of_computation (ictx_t* ic)
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

static int_action_t
apply_cont (ictx_t* ic)
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
      push_cont (ret, exp, ic);
      return eval_error (ERR_UNKNOWN_RC);
    }
}

static int_action_t
apply_proc (ictx_t* ic)
{
    Apply_Non_Trapping:
      if (PENDING_INTERRUPTS_P)
        {
          unsigned long interrupts = (PENDING_INTERRUPTS ());
          PREPARE_APPLY_INTERRUPT ();
          SIGNAL_INTERRUPT (interrupts);
        }

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

    Apply_Non_Trapping:
      if (PENDING_INTERRUPTS_P)
        {
          unsigned long interrupts = (PENDING_INTERRUPTS ());
          PREPARE_APPLY_INTERRUPT ();
          SIGNAL_INTERRUPT (interrupts);
        }

    perform_application:
#ifdef APPLY_UCODE_HOOK
      APPLY_UCODE_HOOK ();
#endif
      {
        SCHEME_OBJECT proc = (apply_frame_proc ());

      apply_dispatch:
        switch (OBJECT_TYPE (proc))
          {
          case TC_ENTITY:
            {
              unsigned long frame_size = (apply_frame_size ());
              SCHEME_OBJECT data = (MEMORY_REF (proc, ENTITY_DATA));
              if ((VECTOR_P (data))
                && (frame_size < (VECTOR_LENGTH (data)))
                  && ((VECTOR_REF (data, frame_size)) != SHARP_F)
                  && ((VECTOR_REF (data, 0))
                      == (VECTOR_REF (fixed_objects, ARITY_DISPATCHER_TAG))))
                {
                  (APPLY_FRAME_PROCEDURE ()) = (VECTOR_REF (data, frame_size));
                  goto apply_dispatch;
                }
              (STACK_REF (0)) = (MEMORY_REF (proc, ENTITY_OPERATOR));
              stack_push (make_apply_frame_header (frame_size), ic);

            entity_apply:
              /* This must be done to prevent an infinite push loop by
                 an entity whose handler is the entity itself or some
                 other such loop.  Of course, it will die if stack overflow
                 interrupts are disabled.  */
              STACK_CHECK (0);
              goto internal_apply;
            }

          case TC_RECORD:
            {
              SCHEME_OBJECT applicator = record_applicator(proc);
              if (applicator == SHARP_F)
                APPLICATION_ERROR (ERR_INAPPLICABLE_OBJECT);
              unsigned long frame_size = (APPLY_FRAME_SIZE ());
              (STACK_REF (0)) = applicator;
              PUSH_APPLY_FRAME_HEADER (frame_size);
              goto entity_apply;
            }

          case TC_PROCEDURE:
            {
              unsigned long frame_size = (APPLY_FRAME_SIZE (ic));
              SCHEME_OBJECT lambda = (MEMORY_REF (proc, PROCEDURE_LAMBDA_EXPR));
              {
                SCHEME_OBJECT formals
                  = (MEMORY_REF (lambda, LAMBDA_FORMALS));
                if ((frame_size != (VECTOR_LENGTH (formals)))
                    && (((OBJECT_TYPE (lambda)) != TC_LEXPR)
                        || (frame_size < (VECTOR_LENGTH (formals)))))
                  APPLICATION_ERROR (ERR_WRONG_NUMBER_OF_ARGUMENTS);
              }
              if (GC_NEEDED_P (frame_size + 1))
                {
                  PREPARE_APPLY_INTERRUPT ();
                  IMMEDIATE_GC (frame_size + 1);
                }
              {
                SCHEME_OBJECT * end = (Free + 1 + frame_size);
                SCHEME_OBJECT env
                  = (MAKE_POINTER_OBJECT (TC_ENVIRONMENT, Free));
                (*Free++) = (MAKE_OBJECT (TC_MANIFEST_VECTOR, frame_size));
                (void) stack_pop (stack);
                while (Free < end)
                  (*Free++) = (stack_pop (stack));
                SET_ENV (env);
                REDUCES_TO (lambda_body (lambda));
              }
            }

          case TC_CONTROL_POINT:
            if ((APPLY_FRAME_SIZE ()) != 2)
              APPLICATION_ERROR (ERR_WRONG_NUMBER_OF_ARGUMENTS);
            SET_VAL (* (APPLY_FRAME_ARGS ()));
            unpack_control_point (proc);
            RESET_HISTORY ();
            goto pop_return;

          /* After checking the number of arguments, remove the
             frame header since primitives do not expect it. */

          case TC_PRIMITIVE:
            if (!IMPLEMENTED_PRIMITIVE_P (proc))
              APPLICATION_ERROR (ERR_UNIMPLEMENTED_PRIMITIVE);
            {
              unsigned long n_args = (APPLY_FRAME_N_ARGS ());

              /* Note that the first test below will fail for lexpr
                 primitives.  */

              if (n_args != (PRIMITIVE_ARITY (proc)))
                {
                  if ((PRIMITIVE_ARITY (proc)) != LEXPR_PRIMITIVE_ARITY)
                    APPLICATION_ERROR (ERR_WRONG_NUMBER_OF_ARGUMENTS);
                  SET_LEXPR_ACTUALS (n_args);
                }
              stack_pointer = (APPLY_FRAME_ARGS ());
              SET_EXP (proc);
              APPLY_PRIMITIVE_FROM_INTERPRETER (proc);
              POP_PRIMITIVE_FRAME (n_args);
              goto pop_return;
            }

          case TC_EXTENDED_PROCEDURE:
            {
              SCHEME_OBJECT lambda = (GET_PROCEDURE_LAMBDA (proc));
              unsigned long nnames = (ELAMBDA_N_NAMES (lambda));
              unsigned long reqs = (ELAMBDA_REQS (lambda));
              unsigned long opts = (ELAMBDA_OPTS (lambda));
              unsigned long rest = (ELAMBDA_REST (lambda));
              unsigned long nfixed = (reqs + opts);
              unsigned long naux = (nnames - (nfixed + rest));
              unsigned long nargs
                = (APPLY_FRAME_HEADER_N_ARGS (stack_pop (stack)));

              if ((nargs < reqs) || ((rest == 0) && (nargs > nfixed)))
                {
                  PUSH_APPLY_FRAME_HEADER (nargs);
                  APPLICATION_ERROR (ERR_WRONG_NUMBER_OF_ARGUMENTS);
                }

              unsigned long size = (/* proc: */ 1 + nfixed + rest + naux);
              unsigned long nwords
                = (/* vector header: */ 1
                                        + size
                                        /* rest list: */
                                        + ((nargs > nfixed) ? (2 * (nargs - nfixed)) : 0));
              if (GC_NEEDED_P (nwords))
                {
                  PUSH_APPLY_FRAME_HEADER (nargs);
                  PREPARE_APPLY_INTERRUPT ();
                  IMMEDIATE_GC (nwords);
                }
              SCHEME_OBJECT * scan = Free;
              SCHEME_OBJECT temp = (MAKE_POINTER_OBJECT (TC_ENVIRONMENT, scan));
              (*scan++) = (MAKE_OBJECT (TC_MANIFEST_VECTOR, size));
              if (nargs <= nfixed)
                {
                  (*scan++) = (stack_pop (stack)); // proc
                  for (unsigned int i = 0; i < nargs; i += 1)
                    (*scan++) = (stack_pop (stack));
                  for (unsigned int i = nargs; i < nfixed; i += 1)
                    (*scan++) = DEFAULT_OBJECT;
                  if (rest == 1)
                    (*scan++) = EMPTY_LIST;
                  for (unsigned int i = 0; i < naux; i += 1)
                    (*scan++) = UNASSIGNED_OBJECT;
                }
              else
                {
                  /* assert (rest == 1) */
                  SCHEME_OBJECT list
                    = (MAKE_POINTER_OBJECT (TC_LIST, (scan + size)));
                  (*scan++) = (stack_pop (stack)); // proc
                  for (unsigned int i = 0; i < nfixed; i += 1)
                    (*scan++) = (stack_pop (stack));
                  (*scan++) = list;
                  for (unsigned int i = 0; i < naux; i += 1)
                    (*scan++) = UNASSIGNED_OBJECT;
                  /* Now scan == OBJECT_ADDRESS (list) */
                  for (unsigned int i = nfixed; i < nargs; i += 1)
                    {
                      (*scan++) = (stack_pop (stack));
                      (*scan) = MAKE_POINTER_OBJECT (TC_LIST, (scan + 1));
                      scan += 1;
                    }
                  (scan[-1]) = EMPTY_LIST;
                }
              Free = scan;
              SET_ENV (temp);
              REDUCES_TO (ELAMBDA_BODY (lambda));
            }

#ifdef CC_SUPPORT_P
case TC_COMPILED_ENTRY:
{
  guarantee_cc_return (1 + (APPLY_FRAME_SIZE ()));
  dispatch_code = (apply_compiled_procedure ());

return_from_compiled_code:
  switch (dispatch_code)
    {
    case PRIM_DONE:
      goto pop_return;

    case PRIM_APPLY:
      goto internal_apply;

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
      goto internal_apply;
    }
}
#endif

          default:
            APPLICATION_ERROR (ERR_INAPPLICABLE_OBJECT);
          }
      }

    case RC_JOIN_STACKLETS:
      unpack_control_point (GET_EXP);
      break;

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
      SET_VAL (GET_EXP);
      break;

    /* The following two return codes are both used to restore a
       saved history object.	The difference is that the first does
       not copy the history object while the second does.  In both
       cases, the GET_EXP contains the history object and the
       next item to be popped off the stack contains the offset back
       to the previous restore history return code.  */

    case RC_RESTORE_DONT_COPY_HISTORY:
      {
        prev_restore_history_offset = (OBJECT_DATUM (stack_pop (stack)));
        (void) stack_pop ();
        history_register = (OBJECT_ADDRESS (GET_EXP));
        break;
      }

    case RC_RESTORE_HISTORY:
      {
        if (!restore_history (GET_EXP))
          {
            PUSH_CONT (GET_RET, GET_EXP);
            STACK_CHECK (CONTINUATION_SIZE);
            PUSH_CONT_RC (RC_RESTORE_VALUE, GET_VAL);
            IMMEDIATE_GC (HEAP_AVAILABLE);
          }
        prev_restore_history_offset = (OBJECT_DATUM (stack_pop (stack)));
        (void) stack_pop ();
        if (prev_restore_history_offset > 0)
          (STACK_LOCATIVE_REFERENCE (STACK_BOTTOM,
                                     (-prev_restore_history_offset)))
            = (MAKE_RETURN_CODE (RC_RESTORE_HISTORY));
        break;
      }

    case RC_RESTORE_INT_MASK:
      SET_INTERRUPT_MASK (UNSIGNED_FIXNUM_TO_LONG (GET_EXP));
      if (GC_NEEDED_P (0))
        REQUEST_GC (0);
      if (PENDING_INTERRUPTS_P)
        {
          PUSH_CONT_RC (RC_RESTORE_VALUE, GET_VAL);
          SIGNAL_INTERRUPT (PENDING_INTERRUPTS ());
        }
      break;

    case RC_STACK_MARKER:
      /* Frame consists of the return code followed by two objects.
         The first object has already been popped into GET_EXP,
         so just pop the second argument.  */
      stack_pointer = (STACK_LOCATIVE_OFFSET (stack_pointer, 1));
      break;

    case RC_EXECUTE_SEQUENCE_FINISH:
      end_subproblem ();
      SET_ENV (stack_pop (stack));
      REDUCES_TO_NTH (SEQUENCE_2);

    case RC_SNAP_NEED_THUNK:
      /* Don't snap thunk twice; evaluation of the thunk's body might
         have snapped it already.  */
      if ((MEMORY_REF (GET_EXP, THUNK_SNAPPED)) == SHARP_T)
        SET_VAL (MEMORY_REF (GET_EXP, THUNK_VALUE));
      else
        {
          MEMORY_SET (GET_EXP, THUNK_SNAPPED, SHARP_T);
          MEMORY_SET (GET_EXP, THUNK_VALUE, GET_VAL);
        }
      break;

    default:
      POP_RETURN_ERROR (ERR_INAPPLICABLE_CONTINUATION);
    }
}
