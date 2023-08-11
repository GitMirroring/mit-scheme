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

/* History maintenance data structures and support. */

/* The history consists of a "vertebra" which is a doubly linked ring,
   each entry pointing to a "rib".  The rib consists of a singly
   linked ring whose entries contain expressions and environments. */

static inline SCHEME_OBJECT*
make_history (SCHEME_OBJECT rib, SCHEME_OBJECT next, SCHEME_OBJECT prev)
{
  SCHEME_OBJECT* history = Free;
  *Free++ = rib;
  *Free++ = next;
  *Free++ = prev;
  return history;
}

static inline SCHEME_OBJECT*
make_history_rib (SCHEME_OBJECT exp, SCHEME_OBJECT env, SCHEME_OBJECT next)
{
  SCHEME_OBJECT* rib = Free;
  *Free++ = exp;
  *Free++ = env;
  *Free++ = next;
  return rib;
}

#define history_rib memory_ref_0
#define set_history_rib memory_set_0
#define history_next memory_ref_1
#define set_history_next memory_set_1
#define history_prev memory_ref_2
#define set_history_prev memory_set_2

#define history_rib_exp memory_ref_0
#define set_history_rib_exp memory_set_0
#define history_rib_env memory_ref_1
#define set_history_rib_env memory_set_1
#define history_rib_next memory_ref_2
#define set_history_rib_next memory_set_2

static inline SCHEME_OBJECT
marked_history (SCHEME_OBJECT history)
{
  return OBJECT_NEW_TYPE (MARKED_HISTORY_TYPE, history);
}

static inline SCHEME_OBJECT
unmarked_history (SCHEME_OBJECT history)
{
  return OBJECT_NEW_TYPE (UNMARKED_HISTORY_TYPE, history);
}

static inline bool
marked_history_p (SCHEME_OBJECT history)
{
  return OBJECT_TYPE (history) == MARKED_HISTORY_TYPE;
}

static inline void
mark_history (SCHEME_OBJECT history)
{
  memory_set_1 (history, marked_history (memory_ref_1 (history)));
}

static inline void
mark_history_rib (SCHEME_OBJECT rib)
{
  memory_set_2 (rib, marked_history (memory_ref_2 (rib)));
}

static inline void
unmark_history_rib (SCHEME_OBJECT rib)
{
  memory_set_2 (rib, unmarked_history (memory_ref_2 (rib)));
}
#define READ_DUMMY_HISTORY() (VECTOR_REF (fixed_objects, DUMMY_HISTORY))
#define SAVE_HISTORY_LENGTH (CONTINUATION_SIZE + 2)

#ifndef DISABLE_HISTORY
#  define NEW_SUBPROBLEM new_subproblem
#  define REUSE_SUBPROBLEM reuse_subproblem
#  define NEW_REDUCTION new_reduction
#  define END_SUBPROBLEM end_subproblem
#  define COMPILER_NEW_SUBPROBLEM compiler_new_subproblem
#  define COMPILER_NEW_REDUCTION compiler_new_reduction
#  define COMPILER_END_SUBPROBLEM end_subproblem
#else
#  define NEW_SUBPROBLEM(exp, env) do {} while (false)
#  define REUSE_SUBPROBLEM(exp, env) do {} while (false)
#  define NEW_REDUCTION(exp, env) do {} while (false)
#  define END_SUBPROBLEM() do {} while (false)
#  define COMPILER_NEW_REDUCTION() do {} while (false)
#  define COMPILER_NEW_SUBPROBLEM() do {} while (false)
#  define COMPILER_END_SUBPROBLEM() do {} while (false)
#endif

extern void reset_history (tctx_t*);
extern SCHEME_OBJECT make_dummy_history (void);
extern void save_history (unsigned long, tctx_t*);
extern bool restore_history (SCHEME_OBJECT, tctx_t*);
extern void stop_history (tctx_t*);
extern void new_subproblem (SCHEME_OBJECT, SCHEME_OBJECT, tctx_t*);
extern void reuse_subproblem (SCHEME_OBJECT, SCHEME_OBJECT, tctx_t*);
extern void new_reduction (SCHEME_OBJECT, SCHEME_OBJECT, tctx_t*);
extern void end_subproblem (tctx_t*);
extern void compiler_new_subproblem (tctx_t*);
extern void compiler_new_reduction (tctx_t*);
