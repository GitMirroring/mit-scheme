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

typedef struct interpreter_state_s
{
  struct interpreter_state_s* previous_state;
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
  unsigned long restore_history_offset;

  interpreter_state_t* state;
  long prim_apply_error_code;

  SCHEME_OBJECT primitive;
  SCHEME_OBJECT* primitive_free;
  unsigned long primitive_lexpr_actuals;

} ictx_t;

extern ictx_t* initialize_ictx (unsigned long, SCHEME_OBJECT*);
extern ictx_t* get_ictx (void);
extern void reset_stack (ictx_t*);

static inline void
stack_push (SCHEME_OBJECT obj, ictx_t* ic)
{
  *--ic->stack_pointer = obj;
}

static inline SCHEME_OBJECT
stack_pop (ictx_t* ic)
{
  return *ic->stack_pointer++;
}

static inline SCHEME_OBJECT
stack_ref (unsigned int n, ictx_t* ic)
{
  return ic->stack_pointer[n];
}

static inline SCHEME_OBJECT*
stack_loc (unsigned int n, ictx_t* ic)
{
  return ic->stack_pointer + n;
}

static inline void
stack_set (unsigned int n, SCHEME_OBJECT obj, ictx_t* ic)
{
  ic->stack_pointer[n] = obj;
}

static inline unsigned long
stack_n_pushed (ictx_t* ic)
{
  return ic->stack_end - ic->stack_pointer;
}

static inline SCHEME_OBJECT*
get_sp (ictx_t* ic)
{
  return ic->stack_pointer;
}

static inline void
set_sp (SCHEME_OBJECT* sp, ictx_t* ic)
{
  ic->stack_pointer = sp;
}

static inline void
decrement_sp (unsigned long n, ictx_t* ic)
{
  ic->stack_pointer -= n;
}

static inline void
increment_sp (unsigned long n, ictx_t* ic)
{
  ic->stack_pointer += n;
}

static inline SCHEME_OBJECT*
get_stack_guard (bool stack_overflow_enabled, ictx_t* ic)
{
  return stack_overflow_enabled ? ic->stack_guard : ic->stack_start;
}

static inline SCHEME_OBJECT*
get_stack_end (ictx_t* ic)
{
  return ic->stack_end;
}

static inline bool
stack_can_push_p (unsigned long n, ictx_t* ic)
{
  return (ic->stack_pointer - n) >= ic->stack_guard;
}

static inline bool
stack_overwritten_p (ictx_t* ic)
{
  return *ic->stack_start != (MAKE_BROKEN_HEART (ic->stack_start));
}

static inline unsigned int
n_vals (ictx_t* ic)
{
  return ic->value_pointer - ic->value_store;
}

static inline void
add_val (SCHEME_OBJECT val, ictx_t* ic)
{
  *ic->value_pointer++ = val;
}

static inline SCHEME_OBJECT
get_val (unsigned int n, ictx_t* ic)
{
  return ic->value_store[n];
}

static inline SCHEME_OBJECT
get_single_val (ictx_t* ic)
{
  assert (n_vals (ic) == 1);
  return ic->value_store[0];
}

static inline void
reset_vals (ictx_t* ic)
{
  ic->value_pointer = ic->value_store;
}

static inline SCHEME_OBJECT
get_history (ictx_t* ic)
{
  return *ic->history;
}

static inline void
set_history (SCHEME_OBJECT history, ictx_t* ic)
{
  ic->history = OBJECT_ADDRESS (history);
}

static inline SCHEME_OBJECT
get_restore_history_offset (ictx_t* ic)
{
  return ULONG_TO_FIXNUM (ic->restore_history_offset);
}

static inline void
set_restore_history_offset (SCHEME_OBJECT offset, ictx_t* ic)
{
  ic->restore_history_offset = OBJECT_DATUM (offset);
}

static inline SCHEME_OBJECT*
restore_history_pointer (ictx_t* ic)
{
  return (ic->restore_history_offset == 0)
         ? 0
         : ic->stack_end - ic->restore_history_offset;
}

static inline interpreter_state_t*
interpreter_state (ictx_t* ic)
{
  return ic->state;
}

static inline void
set_interpreter_state (interpreter_state_t* state, ictx_t* ic)
{
  ic->state = state;
}

static inline SCHEME_OBJECT
get_primitive (ictx_t* ic)
{
  return ic->primitive;
}

static inline void
set_primitive (SCHEME_OBJECT primitive, ictx_t* ic)
{
  ic->primitive = primitive;
}

static inline SCHEME_OBJECT*
get_primitive_free (ictx_t* ic)
{
  return ic->primitive_free;
}

static inline void
set_primitive_free (SCHEME_OBJECT* free, ictx_t* ic)
{
  ic->primitive_free = free;
}

static inline unsigned long
primitive_lexpr_actuals (ictx_t* ic)
{
  return ic->primitive_lexpr_actuals;
}

static inline void
set_primitive_lexpr_actuals (unsigned long n, ictx_t* ic)
{
  ic->primitive_lexpr_actuals = n;
}

#endif // SCM_CONTEXT_H
