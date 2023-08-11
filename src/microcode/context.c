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
init_ptctx (ptctx_t* ptctx, sstack_t* stack)
{
  ptctx->stack = stack;
  ptctx->value_pointer = ptctx->value_store;
  set_history
    ((VECTOR_P (fixed_objects) && READ_DUMMY_HISTORY () != SHARP_F)
     ? READ_DUMMY_HISTORY ()
     : make_dummy_history (),
     ptctx);
  ptctx->restore_history_offset = 0;
  ptctx->state = 0;
  ptctx->prim_apply_error_code = PRIM_DONE;
  ptctx->primitive = SHARP_F;
  ptctx->primitive_free = 0;
}

#if 0
static ptctx_t*
new_ptctx (sstack_t* stack)
{
  ptctx_t* ptctx = (malloc (sizeof (ptctx_t)));
  assert (ptctx != 0);
  init_ptctx (ptctx, stack);
  return ptctx;
}
#endif

static ptctx_t default_ptctx_v;
// This will need to be thread local:
static ptctx_t* current_ptctx_v;

ptctx_t*
initialize_ptctx (unsigned long size, SCHEME_OBJECT* block)
{
  initialize_default_stack (size, block);
  init_ptctx (&default_ptctx_v, default_stack ());
  current_ptctx_v = &default_ptctx_v;
  return current_ptctx_v;
}

ptctx_t*
default_ptctx (void)
{
  return &default_ptctx_v;
}

ptctx_t*
current_ptctx (void)
{
  return current_ptctx_v;
}
