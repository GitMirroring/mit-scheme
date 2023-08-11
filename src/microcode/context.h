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

#ifndef SCM_CONTEXT_H
#define SCM_CONTEXT_H 1

#include "object.h"
#include "stack.h"

typedef struct interpreter_state_s
{
  struct interpreter_state_s* previous_state;
  unsigned int nesting_level;
  void* dstack_position;
  jmp_buf catch_env;
  int throw_argument;
} interpreter_state_t;

#define NULL_INTERPRETER_STATE ((interpreter_state_t*) 0)

// Per-thread context
typedef struct
{
  sstack_t* stack;

  SCHEME_OBJECT value_store[64];
  SCHEME_OBJECT* value_pointer;

  SCHEME_OBJECT* history;
  unsigned long restore_history_offset;

  interpreter_state_t* state;
  long prim_apply_error_code;

  SCHEME_OBJECT primitive;
  SCHEME_OBJECT* primitive_free;
  unsigned long primitive_lexpr_actuals;

} ptctx_t;

static inline sstack_t*
ptctx_stack (ptctx_t* c)
{
  return c->stack;
}

static inline unsigned int
n_vals (ptctx_t* c)
{
  return c->value_pointer - c->value_store;
}

static inline void
add_val (SCHEME_OBJECT val, ptctx_t* c)
{
  *c->value_pointer++ = val;
}

static inline SCHEME_OBJECT
get_val (unsigned int n, ptctx_t* c)
{
  return c->value_store[n];
}

static inline SCHEME_OBJECT
get_single_val (ptctx_t* c)
{
  assert (n_vals (c) == 1);
  return c->value_store[0];
}

static inline void
reset_vals (ptctx_t* c)
{
  c->value_pointer = c->value_store;
}

static inline SCHEME_OBJECT
get_history (ptctx_t* c)
{
  return *c->history;
}

static inline void
set_history (SCHEME_OBJECT history, ptctx_t* c)
{
  c->history = OBJECT_ADDRESS (history);
}

static inline SCHEME_OBJECT
get_restore_history_offset (ptctx_t* c)
{
  return ULONG_TO_FIXNUM (c->restore_history_offset);
}

static inline void
set_restore_history_offset (SCHEME_OBJECT offset, ptctx_t* c)
{
  c->restore_history_offset = OBJECT_DATUM (offset);
}

static inline SCHEME_OBJECT*
restore_history_pointer (ptctx_t* c)
{
  return (c->restore_history_offset == 0)
         ? 0
         : stack_end (c->stack) - c->restore_history_offset;
}

static inline interpreter_state_t*
interpreter_state (ptctx_t* c)
{
  return c->state;
}

static inline void
set_interpreter_state (interpreter_state_t* state, ptctx_t* c)
{
  c->state = state;
}

static inline SCHEME_OBJECT
get_primitive (ptctx_t* c)
{
  return c->primitive;
}

static inline void
set_primitive (SCHEME_OBJECT primitive, ptctx_t* c)
{
  c->primitive = primitive;
}

static inline SCHEME_OBJECT*
get_primitive_free (ptctx_t* c)
{
  return c->primitive_free;
}

static inline void
set_primitive_free (SCHEME_OBJECT* free, ptctx_t* c)
{
  c->primitive_free = free;
}

static inline unsigned long
primitive_lexpr_actuals (ptctx_t* c)
{
  return c->primitive_lexpr_actuals;
}

static inline void
set_primitive_lexpr_actuals (unsigned long n, ptctx_t* c)
{
  c->primitive_lexpr_actuals = n;
}

extern ptctx_t* initialize_ptctx (unsigned long, SCHEME_OBJECT*);
extern ptctx_t* default_ptctx (void);
extern ptctx_t* current_ptctx (void);

#endif // SCM_CONTEXT_H
