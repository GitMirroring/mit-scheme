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

typedef enum
{
  INT_ACTION_APPLY_CONT,
  INT_ACTION_APPLY_PROC,
  INT_ACTION_EVAL,
  INT_ACTION_RETURN_FROM_COMPILED_CODE,
  INT_ACTION_DONE
} int_action_t;

static inline void
stack_check (unsigned long n, sstack_t* s)
{
  if (stack_can_push_p (n, s))
    {
      if (stack_overwritten_p (s))
        stack_death ("stack_check");
      REQUEST_INTERRUPT (INT_Stack_Overflow);
    }
}

static inline int_action_t
single_val (SCHEME_OBJECT val, tctx_t* tctx)
{
  reset_vals (tctx);
  add_val (val, tctx);
  return INT_ACTION_APPLY_CONT;
}

static inline void
set_restore_history_offset_and_mark (SCHEME_OBJECT offset, tctx_t* tctx)
{
  set_restore_history_offset (offset, tctx);
  SCHEME_OBJECT* p = restore_history_pointer (tctx);
  if (p != 0)
    *p = MAKE_RETURN_CODE (RC_RESTORE_HISTORY);
}

extern void abort_to_interpreter (int, tctx_t*) NORETURN;
extern int abort_to_interpreter_argument (tctx_t*);

/* Note: push_cont must match the definitions in sdata.h */

static inline void
push_cont (SCHEME_OBJECT ret, SCHEME_OBJECT obj, sstack_t* s)
{
  stack_push (obj, s);
  stack_push (ret, s);
}

static inline void
push_cont_rc (unsigned long rc, SCHEME_OBJECT obj, sstack_t* s)
{
  push_cont ((MAKE_RETURN_CODE (rc)), obj, s);
}

static inline void
push_cont_env (unsigned long rc, SCHEME_OBJECT obj, SCHEME_OBJECT env,
               sstack_t* s)
{
  stack_push (env, s);
  push_cont ((MAKE_RETURN_CODE (rc)), obj, s);
}

static inline SCHEME_OBJECT
make_apply_frame_header (unsigned long size)
{
  return MAKE_OBJECT (TC_MANIFEST_VECTOR, size);
}

static inline unsigned long
apply_frame_header_size (SCHEME_OBJECT header)
{
  return OBJECT_DATUM (header);
}

static inline unsigned long
apply_frame_header_n_args (SCHEME_OBJECT header)
{
  return apply_frame_header_size (header) - 1;
}

static inline SCHEME_OBJECT
apply_frame_header (sstack_t* s)
{
  return stack_ref (0, s);
}

static inline SCHEME_OBJECT
apply_frame_proc (sstack_t* s)
{
  return stack_ref (1, s);
}

static inline void
set_apply_frame_proc (SCHEME_OBJECT proc, sstack_t* s)
{
  return stack_set (1, proc, s);
}

static inline SCHEME_OBJECT
apply_frame_first_arg (sstack_t* s)
{
  return stack_ref (2, s);
}

static inline unsigned long
apply_frame_size (sstack_t* s)
{
  return apply_frame_header_size (apply_frame_header (s));
}

static inline unsigned long
apply_frame_n_args (sstack_t* s)
{
  return apply_frame_header_n_args (apply_frame_header (s));
}

extern void primitive_apply_internal (SCHEME_OBJECT, tctx_t*);

#endif /* not SCM_INTERP_H */
