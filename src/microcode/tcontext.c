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

#include "scheme.h"
#include "history.h"

static void
init_tctx (tctx_t* tctx, unsigned long size, SCHEME_OBJECT* block)
{
  tctx->stack_start = block;
  tctx->stack_end = block + size;
  tctx->stack_guard = tctx->stack_end + STACK_GUARD_SIZE;
  tctx->stack_pointer = tctx->stack_end;
  *tctx->stack_start = (MAKE_BROKEN_HEART (tctx->stack_start));
  tctx->value_pointer = tctx->value_store;
  set_history
    ((VECTOR_P (fixed_objects) && READ_DUMMY_HISTORY () != SHARP_F)
     ? READ_DUMMY_HISTORY ()
     : make_dummy_history (),
     tctx);
  tctx->restore_history_offset = 0;
  tctx->state = 0;
  tctx->prim_apply_error_code = PRIM_DONE;
  tctx->primitive = SHARP_F;
  tctx->primitive_free = 0;
}

#if 0
static tctx_t*
new_tctx (sstack_t* stack)
{
  tctx_t* tctx = (malloc (sizeof (tctx_t)));
  assert (tctx != 0);
  init_tctx (tctx, stack);
  return tctx;
}
#endif

static tctx_t default_tctx_v;
// This will need to be thread local:
static tctx_t* current_tctx_v;

tctx_t*
initialize_tctx (unsigned long size, SCHEME_OBJECT* block)
{
  init_tctx (&default_tctx_v, size, block);
  current_tctx_v = &default_tctx_v;
  return current_tctx_v;
}

tctx_t*
default_tctx (void)
{
  return &default_tctx_v;
}

tctx_t*
current_tctx (void)
{
  return current_tctx_v;
}

void
stack_reset (tctx_t* tctx)
{
  tctx->stack_pointer = tctx->stack_end;
  *tctx->stack_start = (MAKE_BROKEN_HEART (tctx->stack_start));
  tctx->stack_guard = tctx->stack_start + STACK_GUARD_SIZE;
  compiler_setup_interrupt (tctx);
}

void
bind_interpreter_state (interpreter_state_t* new_state, tctx_t* tctx)
{
  interpreter_state_t* state = interpreter_state (tctx);
  new_state->previous_state = state;
  new_state->nesting_level = state->nesting_level;
  new_state->dstack_position = state->dstack_position;
  set_interpreter_state (new_state, tctx);
}

void
unbind_interpreter_state (interpreter_state_t* new_state, tctx_t* tctx)
{
  unsigned long old_mask = GET_INT_MASK;
  SET_INTERRUPT_MASK (0);
  dstack_set_position (new_state->dstack_position);
  SET_INTERRUPT_MASK (old_mask);
  set_interpreter_state (new_state->previous_state, tctx);
}
