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

#ifndef SCM_OSSCHEME_H
#define SCM_OSSCHEME_H 1

#include "outf.h"
#include "os.h"
#include "prims.h"

static inline bool
executing_scheme_primitive_p (tctx_t* tctx)
{
  return PRIMITIVE_P (get_primitive (tctx));
}

static inline void
error_out_of_channels (void)
{
  signal_error_from_primitive (ERR_OUT_OF_FILE_HANDLES, current_tctx ());
}

static inline void
error_out_of_processes (void)
{
  signal_error_from_primitive (ERR_OUT_OF_FILE_HANDLES, current_tctx ());
}

static inline void
error_unimplemented_primitive (void)
{
  signal_error_from_primitive (ERR_UNDEFINED_PRIMITIVE, current_tctx ());
}

static inline void
error_floating_point_exception (void)
{
  signal_error_from_primitive (ERR_FLOATING_OVERFLOW, current_tctx ());
}

static inline void
error_process_terminated (void)
{
  signal_error_from_primitive (ERR_PROCESS_TERMINATED, current_tctx ());
}

static inline void
request_console_resize_interrupt (void)
{
  request_interrupt (INT_Global_3, current_tctx ());
}

static inline void
request_character_interrupt (void)
{
  request_interrupt (INT_Character, current_tctx ());
}

static inline void
request_timer_interrupt (void)
{
  request_interrupt (INT_Timer, current_tctx ());
}

static inline void
request_suspend_interrupt (void)
{
  request_interrupt (INT_Suspend, current_tctx ());
}

static inline bool
pending_interrupts_p (void)
{
  return (INTERRUPT_PENDING_P (INT_Mask));
}

static inline void
deliver_pending_interrupts (void)
{
  if (INTERRUPT_PENDING_P (INT_Mask))
    signal_interrupt_from_primitive (current_tctx ());
}

static inline unsigned long
get_interrupt_mask (void)
{
  return (GET_INT_MASK);
}

extern Tchannel arg_channel (int);

extern void debug_edit_flags (void);
extern void debug_back_trace (outf_channel);
extern void debug_examine_memory (unsigned long, const char*);

#endif /* SCM_OSSCHEME_H */
