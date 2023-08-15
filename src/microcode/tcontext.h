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

#include <setjmp.h>
#include "object.h"

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
  SCHEME_OBJECT* stack_start;
  SCHEME_OBJECT* stack_guard;
  SCHEME_OBJECT* stack_pointer;
  SCHEME_OBJECT* stack_end;

  SCHEME_OBJECT value_store[64];
  SCHEME_OBJECT* value_pointer;

  SCHEME_OBJECT* history;
  unsigned long restore_history_offset;

  interpreter_state_t* state;
  long prim_apply_error_code;

  SCHEME_OBJECT primitive;
  SCHEME_OBJECT* primitive_free;
  unsigned long primitive_lexpr_actuals;

} tctx_t;

static inline SCHEME_OBJECT*
stack_start (tctx_t* tctx)
{
  return tctx->stack_start;
}

static inline void
set_stack_start (SCHEME_OBJECT* sp, tctx_t* tctx)
{
  tctx->stack_start = sp;
}

static inline SCHEME_OBJECT*
stack_end (tctx_t* tctx)
{
  return tctx->stack_end;
}

static inline void
set_stack_end (SCHEME_OBJECT* sp, tctx_t* tctx)
{
  tctx->stack_end = sp;
}

static inline SCHEME_OBJECT*
stack_guard (bool stack_overflow_enabled, tctx_t* tctx)
{
  return stack_overflow_enabled ? tctx->stack_guard : tctx->stack_start;
}

static inline SCHEME_OBJECT*
stack_pointer (tctx_t* tctx)
{
  return tctx->stack_pointer;
}

static inline void
set_stack_pointer (SCHEME_OBJECT* sp, tctx_t* tctx)
{
  tctx->stack_pointer = sp;
}

static inline bool
valid_stack_pointer_p (SCHEME_OBJECT* sp, tctx_t* tctx)
{
  return sp >= tctx->stack_guard && sp <= stack_end (tctx);
}

static inline bool
address_in_stack_p (SCHEME_OBJECT* addr, tctx_t* tctx)
{
  return addr >= stack_start (tctx) && addr < stack_end (tctx);
}

static inline void
stack_push (SCHEME_OBJECT obj, tctx_t* tctx)
{
  *--tctx->stack_pointer = obj;
}

static inline SCHEME_OBJECT
stack_pop (tctx_t* tctx)
{
  return *tctx->stack_pointer++;
}

static inline SCHEME_OBJECT
stack_ref (unsigned int n, tctx_t* tctx)
{
  return tctx->stack_pointer[n];
}

static inline SCHEME_OBJECT*
stack_loc (unsigned int n, tctx_t* tctx)
{
  return tctx->stack_pointer + n;
}

static inline void
stack_set (unsigned int n, SCHEME_OBJECT obj, tctx_t* tctx)
{
  tctx->stack_pointer[n] = obj;
}

static inline unsigned long
stack_n_pushed (tctx_t* tctx)
{
  return tctx->stack_end - tctx->stack_pointer;
}

static inline void
decrement_sp (unsigned long n, tctx_t* tctx)
{
  tctx->stack_pointer -= n;
}

static inline void
increment_sp (unsigned long n, tctx_t* tctx)
{
  tctx->stack_pointer += n;
}

static inline bool
stack_can_push_p (unsigned long n, tctx_t* tctx)
{
  return (tctx->stack_pointer - n) >= tctx->stack_guard;
}

static inline bool
stack_can_pop_p (unsigned long n, tctx_t* tctx)
{
  return (tctx->stack_pointer + n) <= tctx->stack_end;
}

static inline bool
stack_overwritten_p (tctx_t* tctx)
{
  return *tctx->stack_start != (MAKE_BROKEN_HEART (tctx->stack_start));
}

#define SP_TO_N_PUSHED(sp, start, end) ((end) - (sp))
#define N_PUSHED_TO_SP(np, start, end) ((end) - (np))

static inline unsigned int
n_vals (tctx_t* tctx)
{
  return tctx->value_pointer - tctx->value_store;
}

static inline void
add_val (SCHEME_OBJECT val, tctx_t* tctx)
{
  *tctx->value_pointer++ = val;
}

static inline SCHEME_OBJECT
get_val (unsigned int n, tctx_t* tctx)
{
  return tctx->value_store[n];
}

static inline SCHEME_OBJECT
get_single_val (tctx_t* tctx)
{
  assert (n_vals (tctx) == 1);
  return tctx->value_store[0];
}

static inline void
reset_vals (tctx_t* tctx)
{
  tctx->value_pointer = tctx->value_store;
}

static inline SCHEME_OBJECT
get_history (tctx_t* tctx)
{
  return *tctx->history;
}

static inline void
set_history (SCHEME_OBJECT history, tctx_t* tctx)
{
  tctx->history = OBJECT_ADDRESS (history);
}

static inline SCHEME_OBJECT
get_restore_history_offset (tctx_t* tctx)
{
  return ULONG_TO_FIXNUM (tctx->restore_history_offset);
}

static inline void
set_restore_history_offset (SCHEME_OBJECT offset, tctx_t* tctx)
{
  tctx->restore_history_offset = OBJECT_DATUM (offset);
}

static inline SCHEME_OBJECT*
restore_history_pointer (tctx_t* tctx)
{
  return (tctx->restore_history_offset == 0)
         ? 0
         : stack_end (tctx) - tctx->restore_history_offset;
}

static inline interpreter_state_t*
interpreter_state (tctx_t* tctx)
{
  return tctx->state;
}

static inline void
set_interpreter_state (interpreter_state_t* state, tctx_t* tctx)
{
  tctx->state = state;
}

static inline int
interpreter_catch (tctx_t* tctx)
{
  return setjmp (interpreter_state (tctx)->catch_env);
}

static inline void
interpreter_throw (int arg, tctx_t* tctx)
{
  return longjmp (interpreter_state (tctx)->catch_env, arg);
}

static inline long
prim_apply_error_code (tctx_t* tctx)
{
  return tctx->prim_apply_error_code;
}

static inline void
set_prim_apply_error_code (long code, tctx_t* tctx)
{
  tctx->prim_apply_error_code = code;
}

static inline SCHEME_OBJECT
get_primitive (tctx_t* tctx)
{
  return tctx->primitive;
}

static inline void
set_primitive (SCHEME_OBJECT primitive, tctx_t* tctx)
{
  tctx->primitive = primitive;
}

static inline SCHEME_OBJECT*
get_primitive_free (tctx_t* tctx)
{
  return tctx->primitive_free;
}

static inline void
set_primitive_free (SCHEME_OBJECT* free, tctx_t* tctx)
{
  tctx->primitive_free = free;
}

static inline unsigned long
primitive_lexpr_actuals (tctx_t* tctx)
{
  return tctx->primitive_lexpr_actuals;
}

static inline void
set_primitive_lexpr_actuals (unsigned long n, tctx_t* tctx)
{
  tctx->primitive_lexpr_actuals = n;
}

extern tctx_t* initialize_tctx (unsigned long, SCHEME_OBJECT*);
extern tctx_t* default_tctx (void);
extern tctx_t* current_tctx (void);
extern void stack_reset (tctx_t*);
extern void bind_interpreter_state (interpreter_state_t*, tctx_t*);
extern void unbind_interpreter_state (interpreter_state_t*, tctx_t*);

#endif // SCM_CONTEXT_H
