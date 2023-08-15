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
#include "tcontext.h"

static inline void
stack_check (unsigned long n, tctx_t* tctx)
{
  if (stack_can_push_p (n, tctx))
    {
      if (stack_overwritten_p (tctx))
        stack_death ("stack_check");
      REQUEST_INTERRUPT (INT_Stack_Overflow);
    }
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
push_cont (SCHEME_OBJECT ret, SCHEME_OBJECT obj, tctx_t* tctx)
{
  stack_push (obj, tctx);
  stack_push (ret, tctx);
}

static inline void
push_cont_rc (unsigned long rc, SCHEME_OBJECT obj, tctx_t* tctx)
{
  push_cont (MAKE_RETURN_CODE (rc), obj, tctx);
}

static inline void
push_cont_env (unsigned long rc, SCHEME_OBJECT obj, SCHEME_OBJECT env,
               tctx_t* tctx)
{
  stack_push (env, tctx);
  push_cont (MAKE_RETURN_CODE (rc), obj, tctx);
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
apply_frame_header (tctx_t* tctx)
{
  return stack_ref (0, tctx);
}

static inline SCHEME_OBJECT
apply_frame_proc (tctx_t* tctx)
{
  return stack_ref (1, tctx);
}

static inline void
set_apply_frame_proc (SCHEME_OBJECT proc, tctx_t* tctx)
{
  return stack_set (1, proc, tctx);
}

static inline SCHEME_OBJECT
apply_frame_first_arg (tctx_t* tctx)
{
  return stack_ref (2, tctx);
}

static inline unsigned long
apply_frame_size (tctx_t* tctx)
{
  return apply_frame_header_size (apply_frame_header (tctx));
}

static inline unsigned long
apply_frame_n_args (tctx_t* tctx)
{
  return apply_frame_header_n_args (apply_frame_header (tctx));
}

static inline void
primitive_reduce (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check (2, tctx);
  stack_push (env, tctx);
  stack_push (exp, tctx);
  abort_to_interpreter (PRIM_DO_EXPRESSION, tctx);
}

static inline void
primitive_reduce_no_trap (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  stack_check (2, tctx);
  stack_push (env, tctx);
  stack_push (exp, tctx);
  abort_to_interpreter (PRIM_NO_TRAP_EVAL, tctx);
}

extern void interpreter (SCHEME_OBJECT, SCHEME_OBJECT, tctx_t*);
extern void apply_primitive_external (SCHEME_OBJECT, tctx_t*);


#endif /* not SCM_INTERP_H */
