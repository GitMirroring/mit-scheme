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

/* This file contains some macros for defining primitives,
   for argument type or value checking, and for accessing
   the arguments. */

#ifndef SCM_PRIMS_H
#define SCM_PRIMS_H

#include "scheme.h"

/* Definition of primitives. */

#define DEFINE_PRIMITIVE(scheme_name, fn_name, min_args, max_args, doc)	\
SCHEME_OBJECT fn_name (tctx_t* tctx)

/* Can be used for `max_args' in `DEFINE_PRIMITIVE' to indicate that
   the primitive has no upper limit on its arity.  */
#define LEXPR (-1)

/* Primitives should have this as their first statement. */
#ifdef ENABLE_PRIMITIVE_PROFILING
   extern void record_primitive_entry (SCHEME_OBJECT);
#  define PRIMITIVE_HEADER(n_args)                                      \
     record_primitive_entry (get_primitive (tctx))
#else
#  define PRIMITIVE_HEADER(n_args) do {} while (false)
#endif

/* Primitives return by performing one of the following operations. */
#define PRIMITIVE_RETURN(value) return (value)
#define PRIMITIVE_ABORT(code) (abort_to_interpreter ((code), tctx))

static inline void
primitive_reduce (SCHEME_OBJECT exp, SCHEME_OBJECT env, tctx_t* tctx)
{
  add_val (exp, tctx);
  add_val (env, tctx);
  abort_to_interpreter (PRIM_DO_EXPRESSION, tctx);
}

extern void signal_error_from_primitive (long, tctx_t*) NORETURN;
extern void signal_interrupt_from_primitive (tctx_t*) NORETURN;
extern void error_wrong_type_arg (unsigned int) NORETURN;
extern void error_bad_range_arg (unsigned int) NORETURN;
extern void error_external_return (void) NORETURN;
extern void error_with_argument (SCHEME_OBJECT) NORETURN;
extern long arg_integer (unsigned int);
extern intmax_t arg_integer_to_intmax (unsigned int);
extern long arg_nonnegative_integer (unsigned int);
extern long arg_index_integer (unsigned int, long);
extern intmax_t arg_index_integer_to_intmax (unsigned int, intmax_t);
extern long arg_integer_in_range (unsigned int, long, long);
extern unsigned long arg_ulong_integer (unsigned int);
extern unsigned long arg_ulong_index_integer (unsigned int, unsigned long);
extern unsigned long arg_ulong_integer_in_range
  (unsigned int, unsigned long, unsigned long);
extern double arg_real_number (unsigned int);
extern double arg_real_in_range (unsigned int, double, double);
extern long arg_ascii_char (unsigned int);
extern long arg_ascii_integer (unsigned int);

/* Various utilities */

static inline void
primitive_gc (unsigned long amount, tctx_t* tctx)
{
  SCHEME_OBJECT* Free_primitive = get_primitive_free (tctx);
  if (Free_primitive < heap_start)
    {
      outf_fatal
        ("\nMicrocode requested primitive GC outside primitive!\n");
      Microcode_Termination (TERM_EXIT, tctx);
    }
  if (Free < Free_primitive)
    {
      outf_fatal ("\nFree has gone backwards!\n");
      Microcode_Termination (TERM_EXIT, tctx);
    }
  REQUEST_GC (amount + (Free - Free_primitive));
  signal_interrupt_from_primitive (tctx);
}

static inline void
primitive_gc_if_needed (unsigned long amount, tctx_t* tctx)
{
  if (GC_NEEDED_P (amount))
    primitive_gc (amount, tctx);
}

#define Primitive_GC(amount) (primitive_gc ((amount), tctx))
#define Primitive_GC_If_Needed(amount) (primitive_gc_if_needed ((amount), tctx))

#define CHECK_ARG(argument, type_p) do					\
{									\
  if (! (type_p (ARG_REF (argument))))					\
    error_wrong_type_arg (argument);					\
} while (false)

static inline SCHEME_OBJECT
arg_ref (unsigned int n, tctx_t* tctx)
{
  return stack_ref (n - 1, tctx);
}

static inline SCHEME_OBJECT*
arg_loc (unsigned int n, tctx_t* tctx)
{
  return stack_loc (n - 1, tctx);
}

static inline void
pop_primitive_frame (unsigned int arity, tctx_t* tctx)
{
  return increment_sp (arity, tctx);
}

#define ARG_LOC(n) (arg_loc (n, current_tctx ()))
#define ARG_REF(n) (arg_ref (n, current_tctx ()))
#define POP_PRIMITIVE_FRAME(arity)                                      \
  (pop_primitive_frame (arity, current_tctx ()))

#define UNSIGNED_FIXNUM_ARG(arg)					\
  ((FIXNUM_P (ARG_REF (arg)))						\
   ? (UNSIGNED_FIXNUM_TO_LONG (ARG_REF (arg)))				\
   : ((error_wrong_type_arg (arg)), 0))

#define STRING_ARG(arg)							\
  ((STRING_P (ARG_REF (arg)))						\
   ? (STRING_POINTER (ARG_REF (arg)))					\
   : ((error_wrong_type_arg (arg)), ((char *) 0)))

extern unsigned char * arg_extended_string (unsigned int, unsigned long *);

#define BOOLEAN_ARG(arg) ((ARG_REF (arg)) != SHARP_F)

#define CELL_ARG(arg)							\
  ((CELL_P (ARG_REF (arg)))						\
   ? (ARG_REF (arg))							\
   : ((error_wrong_type_arg (arg)), ((SCHEME_OBJECT) 0)))

#define PAIR_ARG(arg)							\
  ((PAIR_P (ARG_REF (arg)))						\
   ? (ARG_REF (arg))							\
   : ((error_wrong_type_arg (arg)), ((SCHEME_OBJECT) 0)))

#define WEAK_PAIR_ARG(arg)						\
  ((WEAK_PAIR_P (ARG_REF (arg)))					\
   ? (ARG_REF (arg))							\
   : ((error_wrong_type_arg (arg)), ((SCHEME_OBJECT) 0)))

#define VECTOR_ARG(arg)							\
  ((VECTOR_P (ARG_REF (arg)))						\
   ? (ARG_REF (arg))							\
   : ((error_wrong_type_arg (arg)), ((SCHEME_OBJECT) 0)))

#define FLOATING_VECTOR_ARG(arg)					\
  ((FLONUM_P (ARG_REF (arg)))						\
   ? (ARG_REF (arg))							\
   : ((error_wrong_type_arg (arg)), ((SCHEME_OBJECT) 0)))

#endif /* SCM_PRIMS_H */
