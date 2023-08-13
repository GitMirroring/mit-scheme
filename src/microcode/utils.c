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

/* This file contains utilities for interrupts, errors, etc. */

#include "scheme.h"
#include "prims.h"
#include "history.h"
#include "syscall.h"
#include "bignmint.h"

SCHEME_OBJECT * history_register;
unsigned long prev_restore_history_offset;

static SCHEME_OBJECT copy_history (SCHEME_OBJECT);
static void error_death (long, const char *) NORETURN;

/* Helper procedures for setup_interrupt, which follows. */

static unsigned long
compute_interrupt_number (unsigned long masked_interrupts)
{
  unsigned long interrupt_number = 0;
  unsigned long bit_mask = 1;
  while ((interrupt_number <= MAX_INTERRUPT_NUMBER)
	 && ((masked_interrupts & bit_mask) == 0))
    {
      interrupt_number += 1;
      bit_mask <<= 1;
    }
  return (interrupt_number);
}

static unsigned long
compute_interrupt_handler_mask (SCHEME_OBJECT interrupt_masks,
				unsigned long interrupt_number)
{
  if ((VECTOR_P (interrupt_masks))
      && (interrupt_number <= (VECTOR_LENGTH (interrupt_masks))))
    {
      SCHEME_OBJECT mask
	= (VECTOR_REF (interrupt_masks, interrupt_number));
      if ((INTEGER_P (mask)) && (integer_to_ulong_p (mask)))
	/* Guarantee that the given interrupt is disabled.  */
	return ((integer_to_ulong (mask)) &~ (1UL << interrupt_number));
    }
  return
    ((interrupt_number <= MAX_INTERRUPT_NUMBER)
     ? ((1UL << interrupt_number) - 1)
     : GET_INT_MASK);
}

static void
terminate_no_interrupt_handler (unsigned long masked_interrupts)
{
  outf_fatal ("\nInterrupts = %#08lx, Mask = %#08lx, Masked = %#08lx\n",
	      GET_INT_CODE,
	      GET_INT_MASK,
	      masked_interrupts);
  Microcode_Termination (TERM_NO_INTERRUPT_HANDLER);
}

SCHEME_OBJECT
initialize_interrupt_handler_vector (void)
{
  return (make_vector ((MAX_INTERRUPT_NUMBER + 2), SHARP_F, false));
}

SCHEME_OBJECT
initialize_interrupt_mask_vector (void)
{
  SCHEME_OBJECT v = (make_vector ((MAX_INTERRUPT_NUMBER + 2), SHARP_F, false));
  unsigned long interrupt_number = 0;
  while (interrupt_number <= MAX_INTERRUPT_NUMBER)
    {
      VECTOR_SET (v,
		  interrupt_number,
		  (ulong_to_integer ((1UL << interrupt_number) - 1)));
      interrupt_number += 1;
    }
  return (v);
}

/* setup_interrupt is called from the SIGNAL_INTERRUPT macro to do all
   of the setup for calling the user's interrupt routines. */

void
setup_interrupt (unsigned long masked_interrupts, tctx_t* tctx)
{
  if (!VECTOR_P (fixed_objects))
    {
      outf_fatal ("\nInvalid fixed-objects vector");
      terminate_no_interrupt_handler (masked_interrupts);
    }
  unsigned long interrupt_number
    = compute_interrupt_number (masked_interrupts);
  SCHEME_OBJECT interrupt_handlers
    = VECTOR_REF (fixed_objects, SYSTEM_INTERRUPT_VECTOR);
  SCHEME_OBJECT interrupt_masks
    = VECTOR_REF (fixed_objects, FIXOBJ_INTERRUPT_MASK_VECTOR);
  if (! (VECTOR_P (interrupt_handlers)
	 && interrupt_number < VECTOR_LENGTH (interrupt_handlers)))
    {
      outf_fatal ("\nUnable to get interrupt handler.");
      terminate_no_interrupt_handler (masked_interrupts);
    }
  unsigned long interrupt_mask
    = compute_interrupt_handler_mask (interrupt_masks, interrupt_number);
  SCHEME_OBJECT interrupt_handler
    = VECTOR_REF (interrupt_handlers, interrupt_number);

  stop_history (tctx);
  sstack_t* s = tctx_stack (tctx);
  preserve_interrupt_mask (s);

  /* Now make an environment frame for use in calling the
     user supplied interrupt routine.  It will be given two arguments:
     the UNmasked interrupt requests, and the currently enabled
     interrupts.  */
  stack_check (STACK_ENV_EXTRA_SLOTS + 3, s);
  stack_push (ULONG_TO_FIXNUM (GET_INT_MASK), s);
  stack_push (ULONG_TO_FIXNUM (GET_INT_CODE), s);
  stack_push (interrupt_handler, s);
  stack_push (make_apply_frame_header (3), s);

  /* Turn off interrupts: */
  SET_INTERRUPT_MASK (interrupt_mask);
}

/* Error processing utilities */

void
err_print (long error_code, outf_channel where)
{
  const char * message
    = ((error_code <= MAX_ERROR)
       ? (Error_Names[error_code])
       : 0);
  if (message == 0)
    outf (where, "Unknown error code %#lx.\n", error_code);
  else
    outf (where, "Error code %#lx (%s).\n", error_code, message);
}

long death_blow;

static void
error_death (long code, const char * message)
{
  death_blow = code;
  outf_fatal ("\nMicrocode Error: %s.\n", message);
  err_print (code, FATAL_OUTPUT);
  outf_error ("\n**** Stack Trace ****\n\n");
  Back_Trace (ERROR_OUTPUT, stack_pointer (current_stack ()));
  termination_no_error_handler ();
  /*NOTREACHED*/
}

void
Stack_Death (tctx_t* tctx)
{
  outf_fatal("\nWill_Push vs. Pushed inconsistency.\n");
  Microcode_Termination (TERM_BAD_STACK);
  /*NOTREACHED*/
}

void
preserve_interrupt_mask (sstack_t* s)
{
  stack_check (CONTINUATION_SIZE, s);
  push_cont_rc (RC_RESTORE_INT_MASK, ULONG_TO_FIXNUM (GET_INT_MASK), s);
}

/* canonicalize_primitive_context should be used by "unsafe"
   primitives to guarantee that their execution context is the
   expected one, ie.  they are called from the interpreter.  If they
   are called from compiled code, they should abort to the interpreter
   and reenter.  */

void
canonicalize_primitive_context (tctx_t* tctx)
{
  sstack_t* s = tctx_stack (tctx);
  SCHEME_OBJECT primitive = get_primitive (tctx);
  assert (PRIMITIVE_P (primitive));
  unsigned long n_args = (PRIMITIVE_N_ARGUMENTS (primitive));

#ifdef CC_SUPPORT_P
  if (CC_RETURN_P (stack_ref (n_args, s)))
    {
      /* The primitive has been invoked from compiled code. */
      stack_push (primitive, s);
      stack_push (make_apply_frame_header (n_args + 1), s);
      guarantee_interp_return ();
      set_primitive (SHARP_F, tctx);
      abort_to_interpreter (PRIM_APPLY, tctx);
      /*NOTREACHED*/
    }
#endif

  assert (RETURN_CODE_P (stack_ref (n_args, s)));
}

/* back_out_of_primitive sets the registers up so that the backout
   mechanism in "interp.c" will cause the primitive to be
   restarted if the error/interrupt is proceeded.  */

void
back_out_of_primitive (tctx_t* tctx)
{
  sstack_t* s = tctx_stack (tctx);
  SCHEME_OBJECT prim = get_primitive (tctx);
  assert (PRIMITIVE_P (prim));
  stack_push (prim, s);
  stack_push (make_apply_frame_header (PRIMITIVE_N_ARGUMENTS (prim) + 1), s);
  guarantee_interp_return ();
  set_primitive (SHARP_F, tctx);
  push_cont_rc (RC_INTERNAL_APPLY, SHARP_F, s);
}

/* Useful error procedures */

/* Note that backing out of the primitives happens after aborting,
   not before.
   This guarantees that the interpreter state is consistent, since the
   longjmp restores the relevant registers even if the primitive was
   invoked from compiled code. */

void
signal_error_from_primitive (long error_code, tctx_t* tctx)
{
  abort_to_interpreter (error_code, tctx);
}

void
signal_interrupt_from_primitive (tctx_t* tctx)
{
  abort_to_interpreter (PRIM_INTERRUPT, tctx);
  /*NOTREACHED*/
}

void
error_wrong_type_arg (int n)
{
  long error_code;

  switch (n)
    {
    case 1: error_code = ERR_ARG_1_WRONG_TYPE; break;
    case 2: error_code = ERR_ARG_2_WRONG_TYPE; break;
    case 3: error_code = ERR_ARG_3_WRONG_TYPE; break;
    case 4: error_code = ERR_ARG_4_WRONG_TYPE; break;
    case 5: error_code = ERR_ARG_5_WRONG_TYPE; break;
    case 6: error_code = ERR_ARG_6_WRONG_TYPE; break;
    case 7: error_code = ERR_ARG_7_WRONG_TYPE; break;
    case 8: error_code = ERR_ARG_8_WRONG_TYPE; break;
    case 9: error_code = ERR_ARG_9_WRONG_TYPE; break;
    case 10: error_code = ERR_ARG_10_WRONG_TYPE; break;
    default: error_code = ERR_EXTERNAL_RETURN; break;
    }
  signal_error_from_primitive (error_code, current_tctx ());
}

void
error_bad_range_arg (int n)
{
  long error_code;

  switch (n)
    {
    case 1: error_code = ERR_ARG_1_BAD_RANGE; break;
    case 2: error_code = ERR_ARG_2_BAD_RANGE; break;
    case 3: error_code = ERR_ARG_3_BAD_RANGE; break;
    case 4: error_code = ERR_ARG_4_BAD_RANGE; break;
    case 5: error_code = ERR_ARG_5_BAD_RANGE; break;
    case 6: error_code = ERR_ARG_6_BAD_RANGE; break;
    case 7: error_code = ERR_ARG_7_BAD_RANGE; break;
    case 8: error_code = ERR_ARG_8_BAD_RANGE; break;
    case 9: error_code = ERR_ARG_9_BAD_RANGE; break;
    case 10: error_code = ERR_ARG_10_BAD_RANGE; break;
    default: error_code = ERR_EXTERNAL_RETURN; break;
    }
  signal_error_from_primitive (error_code, current_tctx ());
}

void
error_external_return (void)
{
  signal_error_from_primitive (ERR_EXTERNAL_RETURN, current_tctx ());
}

static SCHEME_OBJECT error_argument;

void
error_with_argument (SCHEME_OBJECT argument)
{
  error_argument = argument;
  signal_error_from_primitive
    ((VECTOR_P (argument)
      && (VECTOR_LENGTH (argument) > 0)
      && VECTOR_REF (argument, 0)
         == LONG_TO_UNSIGNED_FIXNUM (ERR_IN_SYSTEM_CALL))
     ? ERR_IN_SYSTEM_CALL
     : ERR_WITH_ARGUMENT,
     current_tctx ());
  /*NOTREACHED*/
}

void
error_in_system_call (enum syserr_names err, enum syscall_names name)
{
  /* System call errors have some additional information.
     Encode this as a vector in place of the error code.  */
  SCHEME_OBJECT v = (allocate_marked_vector (TC_VECTOR, 3, 0));
  VECTOR_SET (v, 0, (LONG_TO_UNSIGNED_FIXNUM (ERR_IN_SYSTEM_CALL)));
  VECTOR_SET (v, 1, (LONG_TO_UNSIGNED_FIXNUM ((unsigned int) err)));
  VECTOR_SET (v, 2, (LONG_TO_UNSIGNED_FIXNUM ((unsigned int) name)));
  error_argument = v;
  signal_error_from_primitive (ERR_IN_SYSTEM_CALL, current_tctx ());
  /*NOTREACHED*/
}

void
error_system_call (int code, enum syscall_names name)
{
  error_in_system_call ((OS_error_code_to_syserr (code)), name);
  /*NOTREACHED*/
}

long
arg_integer (int arg_number)
{
  SCHEME_OBJECT object = (ARG_REF (arg_number));
  if (! (INTEGER_P (object)))
    error_wrong_type_arg (arg_number);
  if (! (integer_to_long_p (object)))
    error_bad_range_arg (arg_number);
  return (integer_to_long (object));
}

intmax_t
arg_integer_to_intmax (int arg_number)
{
  SCHEME_OBJECT object = (ARG_REF (arg_number));
  if (! (INTEGER_P (object)))
    error_wrong_type_arg (arg_number);
  if (! (integer_to_intmax_p (object)))
    error_bad_range_arg (arg_number);
  return (integer_to_intmax (object));
}

long
arg_nonnegative_integer (int arg_number)
{
  long result = (arg_integer (arg_number));
  if (result < 0)
    error_bad_range_arg (arg_number);
  return (result);
}

long
arg_index_integer (int arg_number, long upper_limit)
{
  long result = (arg_integer (arg_number));
  if ((result < 0) || (result >= upper_limit))
    error_bad_range_arg (arg_number);
  return (result);
}

intmax_t
arg_index_integer_to_intmax (int arg_number, intmax_t upper_limit)
{
  intmax_t result = (arg_integer_to_intmax (arg_number));
  if ((result < 0) || (result >= upper_limit))
    error_bad_range_arg (arg_number);
  return (result);
}

long
arg_integer_in_range (int arg_number, long lower_limit, long upper_limit)
{
  long result = (arg_integer (arg_number));
  if ((result < lower_limit) || (result >= upper_limit))
    error_bad_range_arg (arg_number);
  return (result);
}

unsigned long
arg_ulong_integer (int arg_number)
{
  SCHEME_OBJECT object = (ARG_REF (arg_number));
  if (! (INTEGER_P (object)))
    error_wrong_type_arg (arg_number);
  if (! (integer_to_ulong_p (object)))
    error_bad_range_arg (arg_number);
  return (integer_to_ulong (object));
}

unsigned long
arg_ulong_index_integer (int arg_number, unsigned long upper_limit)
{
  unsigned long result = (arg_ulong_integer (arg_number));
  if (result >= upper_limit)
    error_bad_range_arg (arg_number);
  return (result);
}

unsigned long
arg_ulong_integer_in_range (int arg_number,
			    unsigned long lower_limit,
			    unsigned long upper_limit)
{
  unsigned long result = (arg_ulong_integer (arg_number));
  if (! ((result >= lower_limit) && (result < upper_limit)))
    error_bad_range_arg (arg_number);
  return (result);
}

bool
real_number_to_double_p (SCHEME_OBJECT x)
{
  return
    ((BIGNUM_P (x))
     ? (BIGNUM_TO_DOUBLE_P (x))
     : (FLONUM_P (x))
     ? (flonum_is_finite_p (x))
     : true);
}

double
real_number_to_double (SCHEME_OBJECT x)
{
  return
    ((FIXNUM_P (x))
     ? (FIXNUM_TO_DOUBLE (x))
     : (BIGNUM_P (x))
     ? (bignum_to_double (x))
     : (FLONUM_TO_DOUBLE (x)));
}

double
arg_real_number (int arg_number)
{
  SCHEME_OBJECT number = (ARG_REF (arg_number));
  if (! (REAL_P (number)))
    error_wrong_type_arg (arg_number);
  if (! (real_number_to_double_p (number)))
    error_bad_range_arg (arg_number);
  return (real_number_to_double (number));
}

double
arg_real_in_range (int arg_number, double lower_limit, double upper_limit)
{
  double result = (arg_real_number (arg_number));
  if ((result < lower_limit) || (result > upper_limit))
    error_bad_range_arg (arg_number);
  return (result);
}

/* The 32-bit FNV-1a hash, short for Fowler/Noll/Vo in honor of its
   creators.  */

uint32_t
memory_hash (unsigned long length, const void * vp)
{
  const uint8_t * scan = ((const uint8_t *) vp);
  const uint8_t * end = (scan + length);
  uint32_t result = 2166136261U;
  while (scan < end)
    {
      result ^= ((uint32_t) (*scan++));
      result *= 16777619U;
    }
  return (result);
}

bool
hashable_object_p (SCHEME_OBJECT object)
{
  switch (OBJECT_TYPE (object))
    {
    case TC_BYTEVECTOR:
    case TC_CHARACTER_STRING:
    case TC_INTERNED_SYMBOL:
    case TC_UNINTERNED_SYMBOL:
    case TC_BIG_FIXNUM:
    case TC_BIG_FLONUM:
    case TC_RATNUM:
    case TC_COMPLEX:
    case TC_LIST:
    case TC_WEAK_CONS:
    case TC_VECTOR:
    case TC_CELL:
      return (true);
    default:
      return (false);
    }
}

uint32_t
hash_object (SCHEME_OBJECT object)
{
  switch (OBJECT_TYPE (object))
    {
    case TC_BYTEVECTOR:
    case TC_CHARACTER_STRING:
      return (memory_hash ((BYTEVECTOR_LENGTH (object)),
			   (BYTEVECTOR_POINTER (object))));

    case TC_INTERNED_SYMBOL:
    case TC_UNINTERNED_SYMBOL:
      {
	SCHEME_OBJECT name = (MEMORY_REF (object, SYMBOL_NAME));
	return (memory_hash ((BYTEVECTOR_LENGTH (name)),
			     (BYTEVECTOR_POINTER (name))));
      }

    case TC_BIG_FIXNUM:
      return (memory_hash (((BIGNUM_LENGTH (object))
			    * (sizeof (bignum_digit_type))),
			   (BIGNUM_START_PTR (object))));

    case TC_BIG_FLONUM:
      return (memory_hash (((FLOATING_VECTOR_LENGTH (object))
			    * (sizeof (double))),
			   (FLOATING_VECTOR_LOC (object, 0))));

    case TC_RATNUM:
    case TC_COMPLEX:
      return (combine_hashes ((hash_object (MEMORY_REF (object, 0))),
			      (hash_object (MEMORY_REF (object, 1)))));

    case TC_LIST:
    case TC_WEAK_CONS:
      return (combine_hashes ((hash_object (PAIR_CAR (object))),
			      (hash_object (PAIR_CDR (object)))));

    case TC_VECTOR:
      {
	const SCHEME_OBJECT * scan = (VECTOR_LOC (object, 0));
	const SCHEME_OBJECT * end = (scan + (VECTOR_LENGTH (object)));
	uint32_t result = (initial_hash ());
	while (scan < end)
	  result = (combine_hashes (result, (hash_object (*scan++))));
	return result;
      }

    case TC_CELL:
      return (hash_object (MEMORY_REF (object, 0)));

    default:
      return (0);
    }
}

uint32_t
initial_hash (void)
{
  SCHEME_OBJECT object = (VECTOR_REF (fixed_objects, FIXOBJ_INITIAL_HASH));
  if ((FIXNUM_P (object)) && (FIXNUM_TO_ULONG_P (object)))
    {
      unsigned long value = (FIXNUM_TO_ULONG (object));
      if (value <= UINT32_MAX)
        return ((uint32_t) value);
    }
  return 0;
}

uint32_t
combine_hashes (uint32_t hash1, uint32_t hash2)
{
  return ((hash1 * 31) + hash2);
}

bool
interpreter_applicable_p (SCHEME_OBJECT object)
{
 tail_recurse:
  switch (OBJECT_TYPE (object))
    {
    case TC_PRIMITIVE:
    case TC_PROCEDURE:
    case TC_EXTENDED_PROCEDURE:
    case TC_CONTROL_POINT:
      return (true);

    case TC_ENTITY:
      {
	object = entity_operator (object);
	goto tail_recurse;
      }

    case TC_RECORD:
      {
	SCHEME_OBJECT applicator = record_applicator(object);
	if (applicator == SHARP_F)
	  return (false);
	object = applicator;
	goto tail_recurse;
      }

#ifdef CC_SUPPORT_P
    case TC_COMPILED_ENTRY:
      {
	cc_entry_type_t cet;
	return
	  ((read_cc_entry_type ((&cet), (CC_ENTRY_ADDRESS (object))))
	   ? false
	   : ((cet.marker) == CET_PROCEDURE));
      }
#endif
    default:
      return (false);
    }
}

/* Error handling

   It is assumed that any caller of the error code has already
   restored its state to a situation which will make it restartable if
   the error handler returns normally.  As a result, the only work to
   be done on an error is to verify that there is an error handler,
   save the current continuation and create a new one if entered from
   Pop_Return rather than Eval, turn off interrupts, and call it with
   two arguments: the error code and interrupt enables.  */

void
Do_Micro_Error (long error_code, bool from_pop_return_p, tctx_t* tctx)
{
  sstack_t* s = tctx_stack (tctx);
#ifdef ENABLE_DEBUGGING_TOOLS
  if (Print_Errors)
    {
      SCHEME_OBJECT ret = stack_ref (0, s);
      err_print (error_code, ERROR_OUTPUT);
      if (OBJECT_DATUM (ret) == RC_INTERNAL_APPLY
	  || OBJECT_DATUM (ret) == RC_INTERNAL_APPLY_VAL)
	{
	  Print_Expression
            (stack_ref (CONTINUATION_SIZE + STACK_ENV_FUNCTION, s),
	     "Procedure");
	  outf_error ("\n");
	  {
            unsigned long nargs
              = apply_frame_header_n_args
		  (stack_ref (CONTINUATION_SIZE + STACK_ENV_HEADER, s));
	    for (unsigned long i = 0; i < nargs; i += 1)
	      {
		outf_error ("Argument %ld: ", i + 1);
		Print_Expression
                  (stack_ref (CONTINUATION_SIZE + STACK_ENV_FIRST_ARG + i, s),
                   "");
		outf_error ("\n");
	      }
	  }
	}
      else
	{
	  Print_Expression (stack_ref (1, s), "Expression");
	  outf_error ("\n");
          SCHEME_OBJECT env = stack_ref (2, s);
          if (GLOBAL_FRAME_P (env) || PROCEDURE_FRAME_P (env))
            {
	      Print_Expression (env, "Environment");
	      outf_error ("\n");
            }
	}
      Print_Return (ret, "Return code");
      outf_error ("\n");
    }
#endif

  if (Trace_On_Error)
    {
      outf_error ("\n\n**** Stack Trace ****\n\n");
      Back_Trace (ERROR_OUTPUT, stack_pointer (s));
    }

#ifdef ENABLE_DEBUGGING_TOOLS
  {
    unsigned int* from = local_circle;
    unsigned int* end = from + local_nslots;
    unsigned int* to = debug_circle;
    while (from < end)
      *to++ = *from++;
  }
  debug_nslots = local_nslots;
  debug_slotno = local_slotno;
#endif

  if (from_pop_return_p)
    {
      stack_check (CONTINUATION_SIZE, s);
      push_cont_rc (RC_POP_RETURN_ERROR, get_single_val (tctx), s);
    }
  else
    {
      stack_check (CONTINUATION_SIZE + 1, s);
      push_cont_env (RC_EVAL_ERROR, stack_ref (1, s), stack_ref (2, s), s);
    }

  SCHEME_OBJECT handler = SHARP_F;
  {
    SCHEME_OBJECT error_vector
      = VECTOR_P (fixed_objects)
        ? VECTOR_REF (fixed_objects, SYSTEM_ERROR_VECTOR)
        : SHARP_F;
    if (!VECTOR_P (error_vector))
      error_death (error_code, "No error handlers");
    if (error_code >= 0 && error_code < (VECTOR_LENGTH (error_vector)))
      handler = VECTOR_REF (error_vector, error_code);
    else if (ERR_BAD_ERROR_CODE < VECTOR_LENGTH (error_vector))
      handler = VECTOR_REF (error_vector, ERR_BAD_ERROR_CODE);
    else
      error_death (error_code, "No error handlers");
  }

  /* Return from error handler will re-enable interrupts & restore history */
  stop_history (tctx);
  preserve_interrupt_mask (s);

  stack_check (STACK_ENV_EXTRA_SLOTS + 3, s);
  /* Arg 2:     interrupt mask */
  stack_push (ULONG_TO_FIXNUM (GET_INT_MASK), s);
  /* Arg 1:     error code  */
  if (error_code == ERR_WITH_ARGUMENT || error_code == ERR_IN_SYSTEM_CALL)
    stack_push (error_argument, s);
  else
    stack_push (long_to_integer (error_code), s);
  stack_push (handler, s);
  stack_push (make_apply_frame_header (3), s);

  /* Disable all interrupts */
  SET_INTERRUPT_MASK (0);
}

/* History */

void
reset_history (tctx_t* tctx)
{
  set_history
    (((VECTOR_P (fixed_objects) && (READ_DUMMY_HISTORY () != SHARP_F))
      ? READ_DUMMY_HISTORY ()
      : make_dummy_history ()),
     tctx);
  set_restore_history_offset (ULONG_TO_FIXNUM (0), tctx);
}

SCHEME_OBJECT
make_dummy_history (void)
{
  SCHEME_OBJECT rib
    = MAKE_POINTER_OBJECT (UNMARKED_HISTORY_TYPE,
                           make_history_rib (SHARP_F, SHARP_F, SHARP_F));
  set_history_rib_next (rib, rib);
  SCHEME_OBJECT history
    = MAKE_POINTER_OBJECT (UNMARKED_HISTORY_TYPE,
                           make_history (rib, SHARP_F, SHARP_F));
  set_history_next (history, history);
  set_history_prev (history, history);
  return history;
}

/* save_history places a restore history frame on the stack. Such a
   frame consists of a normal continuation frame plus a pointer to the
   stacklet on which the last restore history is located and the
   offset within that stacklet.  If the last restore history is in
   this stacklet then the history pointer is #F to signify this.  If
   there is no previous restore history then the history pointer is #F
   and the offset is 0. */

void
save_history (unsigned long rc, tctx_t* tctx)
{
  sstack_t* s = tctx_stack (tctx);
  stack_check (HISTORY_SIZE, s);
  stack_push (SHARP_F, s);      // obsolete field
  stack_push (get_restore_history_offset (tctx), s);
  push_cont_rc (rc, unmarked_history (get_history (tctx)), s);
  set_history (READ_DUMMY_HISTORY (), tctx);
}

/* restore_history pops a history object off the stack and makes a
   copy of it the current history collection object.  This is called
   only from the RC_RESTORE_HISTORY case in "interp.c".  */

bool
restore_history (SCHEME_OBJECT history, tctx_t* tctx)
{
  SCHEME_OBJECT new_history = copy_history (history);
  if (new_history == SHARP_F)
    return (false);
  set_history (new_history, tctx);
  return (true);
}

/* The entire trick to history is right here: it is either copied or
   reused when restored.  Initially, stop_history marks the stack so
   that the history will merely be popped and reused.  On a catch,
   however, the return code is changed to force the history to be
   copied instead.  Thus, histories saved as part of a control point
   are not side-effected in the history collection process.  */

void
stop_history (tctx_t* tctx)
{
  save_history (RC_RESTORE_DONT_COPY_HISTORY, tctx);
  set_restore_history_offset (stack_n_pushed (tctx_stack (tctx)), tctx);
}

void
new_subproblem (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  SCHEME_OBJECT history = history_next (get_history (tctx));
  SCHEME_OBJECT rib = history_rib (history);
  mark_history (history);
  set_history_rib_exp (rib, exp);
  set_history_rib_env (rib, env);
  mark_history_rib (rib);
  set_history (history, tctx);
}

void
reuse_subproblem (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  SCHEME_OBJECT rib = history_rib (get_history (tctx));
  set_history_rib_exp (rib, exp);
  set_history_rib_env (rib, env);
  mark_history_rib (rib);
}

void
new_reduction (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  SCHEME_OBJECT history = get_history (tctx);
  SCHEME_OBJECT next = history_rib_next (history_rib (history));
  set_history_rib_exp (next, exp);
  set_history_rib_env (next, env);
  unmark_history_rib (next);
  set_history_rib (history, unmarked_history (next));
}

void
end_subproblem (tctx_t* tctx)
{
  SCHEME_OBJECT history = get_history (tctx);
  unmark_history (history);
  set_history (history_prev (history), tctx);
}

void
compiler_new_subproblem (tctx_t* tctx)
{
  new_subproblem (SHARP_F, (MAKE_RETURN_CODE (RC_POP_FROM_COMPILED_CODE)), tctx);
}

void
compiler_new_reduction (tctx_t* tctx)
{
  new_reduction (SHARP_F, (MAKE_RETURN_CODE (RC_POP_FROM_COMPILED_CODE)), tctx);
}

/* Returns SHARP_F if insufficient space available.  */

static unsigned long
history_elt_size (SCHEME_OBJECT rib)
{
  unsigned long size = 6;
  SCHEME_OBJECT scan_rib = history_rib_next (rib);
  while (scan_rib != rib)
    {
      size += 3;
      scan_rib = history_rib_next (rib);
    }
  return size;
}

static unsigned long
history_size (SCHEME_OBJECT history)
{
  unsigned long size = history_elt_size (history);
  SCHEME_OBJECT scan = history_next (history);
  while (scan != history)
    {
      size += history_elt_size (scan);
      scan = history_next (history);
    }
  return size;
}

static SCHEME_OBJECT
copy_rib (SCHEME_OBJECT rib)
{
  SCHEME_OBJECT new_rib
    = make_history_rib (history_rib_exp (rib), history_rib_env (rib), SHARP_F);
  SCHEME_OBJECT prev = new_rib;
  SCHEME_OBJECT scan = history_rib_next (rib);
  while (scan != rib)
    {
      SCHEME_OBJECT next
        = make_history_rib (history_rib_exp (scan),
                            history_rib_env (scan),
                            SHARP_F);
      set_history_rib_next
        (prev,
         (OBJECT_NEW_TYPE (OBJECT_TYPE (history_next (scan)),
                           next)));
      prev = next;
      scan = history_rib_next (scan);
    }
  set_history_rib_next
    (prev,
     (OBJECT_NEW_TYPE (OBJECT_TYPE (history_next (rib)),
                       new_rib)));
  return new_rib;
}

static SCHEME_OBJECT
copy_history (SCHEME_OBJECT history)
{
  assert (HUNK3_P (history));

  if (SPACE_BEFORE_GC () < history_size (history))
    return (SHARP_F);

  SCHEME_OBJECT new_history
    = make_history (copy_rib (history_rib (history)), SHARP_F, SHARP_F);
  SCHEME_OBJECT prev = new_history;
  SCHEME_OBJECT scan = history_next (history);
  while (scan != history)
    {
      SCHEME_OBJECT next = make_history (SHARP_F, SHARP_F, prev);
      set_history_next
        (prev,
         (OBJECT_NEW_TYPE (OBJECT_TYPE (history_next (scan)),
                           next)));
      prev = next;
      scan = history_next (scan);
    }
  set_history_next
    (prev,
     (OBJECT_NEW_TYPE (OBJECT_TYPE (history_next (history)),
                       new_history)));
  set_history_prev (history, prev);
  return new_history;
}

#ifdef ENABLE_PRIMITIVE_PROFILING

/* The profiling mechanism is enabled by storing a vector in the fixed
   objects vector.  The vector should be initialized to contain all
   zeros.  */

void
record_primitive_entry (SCHEME_OBJECT primitive)
{

  if (VECTOR_P (fixed_objects))
    {
      SCHEME_OBJECT table
	= (VECTOR_REF (fixed_objects, Primitive_Profiling_Table));
      if (VECTOR_P (table))
	{
	  unsigned long index = (OBJECT_DATUM (primitive));
	  VECTOR_SET (table,
		      index,
		      (ulong_to_integer
		       (1 + (integer_to_ulong (VECTOR_REF (table, index))))));
	}
    }
}

#endif /* ENABLE_PRIMITIVE_PROFILING */

#ifdef __WIN32__

#include <windows.h>

SCHEME_OBJECT
Compiler_Get_Fixed_Objects (void)
{
  return ((VECTOR_P (fixed_objects)) ? fixed_objects : SHARP_F);
}

extern SCHEME_OBJECT Re_Enter_Interpreter (void);
extern SCHEME_OBJECT C_call_scheme
  (SCHEME_OBJECT, long, SCHEME_OBJECT *);

SCHEME_OBJECT
C_call_scheme (SCHEME_OBJECT proc,
       long n_args,
       SCHEME_OBJECT * argvec)
{
  SCHEME_OBJECT primitive, prim_lexpr, * sp, result;
  SCHEME_OBJECT * callers_last_return_code;

#ifdef CC_IS_NATIVE
  extern void * C_Frame_Pointer;
  extern void * C_Stack_Pointer;
  void * cfp = C_Frame_Pointer;
  void * csp = C_Stack_Pointer;
#ifdef CL386
  __try
#endif
#endif
  {
    primitive = GET_PRIMITIVE;
    prim_lexpr = GET_LEXPR_ACTUALS;
    callers_last_return_code = last_return_code;

    if (! (PRIMITIVE_P (primitive)))
      abort_to_interpreter (ERR_CANNOT_RECURSE);
      /*NOTREACHED*/
    sp = stack_pointer;

   Will_Push ((2 * CONTINUATION_SIZE) + (n_args + STACK_ENV_EXTRA_SLOTS + 1));
    {
      long i;

      SET_RC (RC_END_OF_COMPUTATION);
      SET_EXP (primitive);
      SAVE_CONT ();

      for (i = n_args; --i >= 0; )
	STACK_PUSH (argvec[i]);
      STACK_PUSH (proc);
      PUSH_APPLY_FRAME_HEADER (n_args);

      SET_RC (RC_INTERNAL_APPLY);
      SET_EXP (SHARP_F);
      SAVE_CONT ();
    }
   Pushed ();
    result = (Re_Enter_Interpreter ());

    if (stack_pointer != sp)
      signal_error_from_primitive (ERR_STACK_HAS_SLIPPED);
      /*NOTREACHED*/

    last_return_code = callers_last_return_code;
    SET_LEXPR_ACTUALS (prim_lexpr);
    SET_PRIMITIVE (primitive);
  }
#ifdef CC_IS_NATIVE
#ifdef CL386
  __finally
#endif
  {
    C_Frame_Pointer = cfp;
    C_Stack_Pointer = csp;
  }
#endif

  return  result;
}

#endif /* __WIN32__ */

void
set_ptr_register (unsigned int index, SCHEME_OBJECT * p)
{
  (Registers[index]) = ((SCHEME_OBJECT) p);
}

void
set_ulong_register (unsigned int index, unsigned long value)
{
  (Registers[index]) = ((SCHEME_OBJECT) value);
}
