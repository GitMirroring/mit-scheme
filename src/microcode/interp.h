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

/* Definitions used by the interpreter and some utilities. */

#ifndef SCM_INTERP_H
#define SCM_INTERP_H 1

#include "object.h"
#include "stack.h"

typedef struct
{
  interpreter_state_t previous_state;
  unsigned int nesting_level;
  void* dstack_position;
  jmp_buf catch_env;
  int throw_argument;
} interpreter_state_t;

#define NULL_INTERPRETER_STATE ((interpreter_state_t*) 0)

// Interpreter context
typedef struct
{
  SCHEME_OBJECT* stack_start;
  SCHEME_OBJECT* stack_guard;
  SCHEME_OBJECT* stack_pointer;
  SCHEME_OBJECT* stack_end;

  SCHEME_OBJECT value_store[64];
  SCHEME_OBJECT* value_pointer;

  SCHEME_OBJECT* history;
  unsigned long prev_restore_history_offset;

  interpreter_state_t* state;
  long prim_apply_error_code;

} ictx_t;

typedef enum
{
  INT_ACTION_APPLY_CONT,
  INT_ACTION_APPLY_PROC,
  INT_ACTION_EVAL,
  INT_ACTION_RETURN_FROM_COMPILED_CODE,
  INT_ACTION_DONE
} int_action_t;

extern ictx_t* new_ictx (unsigned long, SCHEME_OBJECT*);

static inline void
stack_push (SCHEME_OBJECT obj, ictx_t* ic)
{
  --(ic->stack_pointer) = obj;
}

static inline SCHEME_OBJECT
stack_pop (ictx_t* ic)
{
  return (ic->stack_pointer)++;
}

static inline void
decrement_sp (unsigned long n, ictx_t* ic)
{
  ic->stack_pointer -= n;
}

static inline SCHEME_OBJECT
stack_ref (unsigned int n, ictx_t* ic)
{
  return ic->stack_pointer[n];
}

static inline SCHEME_OBJECT
stack_loc (unsigned int n, ictx_t* ic)
{
  return ic->stack_pointer + n;
}

static inline void
stack_set (unsigned int n, SCHEME_OBJECT obj, ictx_t* ic)
{
  return ic->stack_pointer[n] = obj;
}

static inline void
stack_check (unsigned long n, ictx_t* ic)
{
  if ((ic->stack_pointer - n) < ic->stack_guard)
    {
      if (*(ic->stack_start) != (make_broken_heart (ic->stack_start)))
        stack_death (ic);
      REQUEST_INTERRUPT (INT_Stack_Overflow);
    }
}

static inline unsigned int
n_vals (ictx_t* ic)
{
  return (ic->value_pointer - ic->value_store);
}

static inline void
add_val (SCHEME_OBJECT val, ictx_t* ic)
{
  (ic->value_pointer)++ = val;
}

static inline SCHEME_OBJECT
get_val (unsigned int n, ictx_t* ic)
{
  return ic->value_store[n];
}

static inline SCHEME_OBJECT
get_single_val (ictx_t* ic)
{
  assert ((n_vals (ic)) == 1);
  return ic->value_store[0];
}

static inline int_action_t
single_val (SCHEME_OBJECT val, ictx_t* ic)
{
  ic->value_pointer = ic->value_store;
  add_val (val, ic);
  return INT_ACTION_APPLY_CONT;
}

/* Note: push_cont must match the definitions in sdata.h */

static inline void
push_cont (SCHEME_OBJECT ret, SCHEME_OBJECT obj, ictx_t* ic)
{
  stack_push (obj, ic);
  stack_push (ret, ic);
}

static inline void
push_cont_rc (unsigned long rc, SCHEME_OBJECT obj, ictx_t* ic)
{
  push_cont ((MAKE_RETURN_CODE (rc)), obj, ic);
}

static inline void
push_cont_env (unsigned long rc, SCHEME_OBJECT obj, SCHEME_OBJECT env,
               ictx_t* ic)
{
  stack_push (env, ic);
  push_cont ((MAKE_RETURN_CODE (rc)), obj, ic);
}

static inline SCHEME_OBJECT
make_apply_frame_header (unsigned long size)
{
  return MAKE_OBJECT (TC_MANIFEST_VECTOR, size);
}

static inline unsigned long
apply_frame_header_size (scheme_object header)
{
  return OBJECT_DATUM (header);
}

static inline unsigned long
apply_frame_header_n_args (scheme_object header)
{
  return apply_frame_header_size (header) - 1;
}

static inline SCHEME_OBJECT
apply_frame_header (ictx_t* ic)
{
  return stack_ref (0, ic);
}

static inline SCHEME_OBJECT
apply_frame_proc (ictx_t* ic)
{
  return stack_ref (1, ic);
}

static inline SCHEME_OBJECT*
apply_frame_args (ictx_t* ic)
{
  return stack_loc (2, ic);
}

static inline unsigned long
apply_frame_size (ictx_t* ic)
{
  return apply_frame_header_size (apply_frame_header (ic));
}

static inline interpreter_state_t*
interpreter_state (ictx_t* ic)
{
  return ic->state;
}

static inline unsigned int
interpreter_nesting_level (ictx_t* ic)
{
  return ic->state->nesting_level;
}

static inline unsigned int
interpreter_nesting_level (ictx_t* ic)
{
  interpreter_state_t* s = ic->state;
  return (s == NULL_INTERPRETER_STATE) ? 0 : (1 + s->nesting_level);
}

static inline jmp_buf
interpreter_catch_env (ictx_t* ic)
{
  return ic->state->catch_env;
}

static inline jmp_buf
interpreter_throw_argument (ictx_t* ic)
{
  return ic->state->throw_argument;
}

extern void abort_to_interpreter (int, ictx_t*) NORETURN;
extern int abort_to_interpreter_argument (ictx_t*);


/* C_call_scheme must save/restore history_register on/from the stack
   so that it will be relocated if the call to Interpret() causes a
   garbage collection. */

#define APPLY_PRIMITIVE_FROM_INTERPRETER PRIMITIVE_APPLY

/* Primitive utility macros */

#ifndef ENABLE_DEBUGGING_TOOLS
#  define PRIMITIVE_APPLY PRIMITIVE_APPLY_INTERNAL
#else
   extern void primitive_apply_internal (SCHEME_OBJECT);
#  define PRIMITIVE_APPLY primitive_apply_internal
#endif

#define PRIMITIVE_APPLY_INTERNAL(primitive) do				\
{									\
  void * PRIMITIVE_APPLY_INTERNAL_position = dstack_position;		\
  SET_PRIMITIVE (primitive);						\
  Free_primitive = Free;						\
  SET_VAL								\
    ((* (Primitive_Procedure_Table [PRIMITIVE_NUMBER (primitive)]))	\
     ());								\
  /* If the primitive failed to unwind the dynamic stack, lose. */	\
  if (PRIMITIVE_APPLY_INTERNAL_position != dstack_position)		\
    {									\
      outf_fatal ("\nPrimitive slipped the dynamic stack: %s\n",	\
		  (PRIMITIVE_NAME (primitive)));			\
      Microcode_Termination (TERM_EXIT);				\
    }									\
  Free_primitive = 0;							\
  SET_PRIMITIVE (SHARP_F);						\
} while (0)

#define POP_PRIMITIVE_FRAME(arity) (stack_pointer = (STACK_LOC (arity)))

#endif /* not SCM_INTERP_H */
