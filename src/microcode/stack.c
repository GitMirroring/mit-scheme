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

#include "const.h"
#include "tcontext.h"
#include "object.h"
#include "stack.h"

static sstack_t default_stack_v;

void
initialize_default_stack (unsigned long size, SCHEME_OBJECT* block)
{
  default_stack_v.start = block;
  default_stack_v.guard = (block + STACK_GUARD_SIZE);
  default_stack_v.end = (block + size);
  default_stack_v.pointer = default_stack_v.end;
  (*block) = (MAKE_BROKEN_HEART (block));
}

sstack_t*
default_stack ()
{
  return &default_stack_v;
}

sstack_t*
current_stack ()
{
  return tctx_stack (current_tctx ());
}

void
stack_reset (sstack_t* s)
{
  s->pointer = s->end;
  *s->start = (MAKE_BROKEN_HEART (s->start));
  s->guard = s->start + STACK_GUARD_SIZE;
  compiler_setup_interrupt (s);
}
