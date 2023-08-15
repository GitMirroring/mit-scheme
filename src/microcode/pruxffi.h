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

/* Headers for the FFI (foreign function interface). */

/* This file declares all of the C functions needed by a shim.  It is
   installed as mit-scheme.h and represents the interface between the
   shims and the machine.  It should not include any other headers,
   and should minimize dependencies on the exact configuration of the
   machine.  Thus it declares teensy functions like empty_list(). */

#include <stddef.h>

/* This is redundant, but avoids the need for object.h, config.h, types.h... */
typedef unsigned long SCM;

extern char* cstack_top (void);
extern void cstack_push (void*, size_t);
extern char* cstack_lpop (char*, size_t);
extern void cstack_pop (char*);

#define CSTACK_PUSH(TYPE, VAR)                                          \
  cstack_push ((void*) &VAR, sizeof (TYPE));

/* "Local" CStack pops keep the top-of-stack in a local variable
   (TOS).  Thus after an abort the trampoline can start again from the
   undisturbed top of the obstack. */
#define CSTACK_LPOP(TYPE, VAR, TOS)					\
  TOS = cstack_lpop (TOS, sizeof (TYPE));				\
  VAR = *((TYPE*) TOS);

typedef SCM (*CalloutTrampOut) (void);
typedef SCM (*CalloutTrampIn) (void);
extern void callout_seal (CalloutTrampIn);
extern void callout_unseal (CalloutTrampIn);
extern SCM callout_continue (CalloutTrampIn);
extern char* callout_lunseal (CalloutTrampIn);
extern void callout_pop (char*);

typedef void (*CallbackKernel) (void);
extern void callback_run_kernel (long, CallbackKernel);
extern char* callback_lunseal (CallbackKernel);
extern void callback_run_handler (long, SCM);
extern void callback_return (char*);

/* Converters. */

extern long arg_long (int);
extern unsigned long arg_ulong (int);
extern double arg_double (int);
extern void* arg_alien_entry (int);
extern void* arg_pointer (int);

extern SCM long_to_scm (const long);
extern SCM ulong_to_scm (const unsigned long);
extern SCM double_to_scm (const double);
extern SCM pointer_to_scm (const void*);
extern SCM struct_to_scm (const void*, int);

extern SCM cons_alien (const void*);

extern long long_value (void);
extern unsigned long ulong_value (void);
extern double double_value (void);
extern void* pointer_value (void);

/* Utilities: */

extern void check_number_of_args (unsigned long);
extern SCM unspecific (void);
extern SCM empty_list (void);
extern int flovec_length (double*);

#ifndef MIT_SCHEME /* Do not include in the microcode, just shims. */
extern SCM cons (SCM car, SCM cdr);
/* For debugging messages from shim code. */
extern void outf_error (const char*, ...);
extern void outf_flush_error (void);
extern void error_external_return (void);
#endif
