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

/* Stack abstraction */

#ifndef SCM_STACK_H
#define SCM_STACK_H 1

#include "object.h"

typedef struct
{
  SCHEME_OBJECT* start;
  SCHEME_OBJECT* guard;
  SCHEME_OBJECT* pointer;
  SCHEME_OBJECT* end;
} sstack_t;

static inline SCHEME_OBJECT*
stack_start (sstack_t* s)
{
  return s->start;
}

static inline void
set_stack_start (SCHEME_OBJECT* sp, sstack_t* s)
{
  s->start = sp;
}

static inline SCHEME_OBJECT*
stack_end (sstack_t* s)
{
  return s->end;
}

static inline void
set_stack_end (SCHEME_OBJECT* sp, sstack_t* s)
{
  s->end = sp;
}

static inline SCHEME_OBJECT*
stack_guard (bool stack_overflow_enabled, sstack_t* s)
{
  return stack_overflow_enabled ? s->guard : s->start;
}

static inline SCHEME_OBJECT*
stack_pointer (sstack_t* s)
{
  return s->pointer;
}

static inline void
set_stack_pointer (SCHEME_OBJECT* sp, sstack_t* s)
{
  s->pointer = sp;
}

static inline void
stack_push (SCHEME_OBJECT obj, sstack_t* s)
{
  *--s->pointer = obj;
}

static inline SCHEME_OBJECT
stack_pop (sstack_t* s)
{
  return *s->pointer++;
}

static inline SCHEME_OBJECT
stack_ref (unsigned int n, sstack_t* s)
{
  return s->pointer[n];
}

static inline SCHEME_OBJECT*
stack_loc (unsigned int n, sstack_t* s)
{
  return s->pointer + n;
}

static inline void
stack_set (unsigned int n, SCHEME_OBJECT obj, sstack_t* s)
{
  s->pointer[n] = obj;
}

static inline unsigned long
stack_n_pushed (sstack_t* s)
{
  return s->end - s->pointer;
}

static inline void
decrement_sp (unsigned long n, sstack_t* s)
{
  s->pointer -= n;
}

static inline void
increment_sp (unsigned long n, sstack_t* s)
{
  s->pointer += n;
}

static inline bool
stack_can_push_p (unsigned long n, sstack_t* s)
{
  return (s->pointer - n) >= s->guard;
}

static inline bool
stack_can_pop_p (unsigned long n, sstack_t* s)
{
  return (s->pointer + n) <= s->end;
}

static inline bool
stack_overwritten_p (sstack_t* s)
{
  return *s->start != (MAKE_BROKEN_HEART (s->start));
}

#define SP_TO_N_PUSHED(sp, start, end) ((end) - (sp))
#define N_PUSHED_TO_SP(np, start, end) ((end) - (np))

// #define INITIALIZE_STACK() (stack_reset (get_tctx ()))

extern void initialize_default_stack (unsigned long, SCHEME_OBJECT*);
extern sstack_t* default_stack (void);
extern sstack_t* current_stack (void);
extern void stack_reset (sstack_t*);

#endif  // SCM_STACK_H
