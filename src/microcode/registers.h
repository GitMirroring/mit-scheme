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

/* The register block */

#ifndef SCM_REGISTERS_H
#define SCM_REGISTERS_H 1

#ifdef __WIN32__
   extern SCHEME_OBJECT* RegistersPtr;
#  define Registers RegistersPtr
#else
   extern SCHEME_OBJECT Registers[];
#endif

// These are the only entries in Registers needed by the microcode.
// All other entries are used only by the compiled code interface.

#define REGBLOCK_MEMTOP			0
#define REGBLOCK_INT_MASK		1
#define REGBLOCK_CC_VAL			2
// #define REGBLOCK_ENV			3
#define REGBLOCK_CC_TEMP		4	/* For use by compiler */
// #define REGBLOCK_EXPR			5
// #define REGBLOCK_RETURN			6
// #define REGBLOCK_LEXPR_ACTUALS		7
// #define REGBLOCK_PRIMITIVE		8
#define REGBLOCK_CLOSURE_FREE		9	/* For use by compiler */
#define REGBLOCK_CLOSURE_SPACE		10	/* For use by compiler */
#define REGBLOCK_STACK_GUARD		11
#define REGBLOCK_INT_CODE		12
#define REGBLOCK_REFLECT_TO_INTERFACE	13	/* For use by compiler */

#define REGBLOCK_MINIMUM_LENGTH		14

#define GET_REG_O(i) (Registers[REGBLOCK_##i])
#define GET_REG_P(i) ((SCHEME_OBJECT*) (Registers[REGBLOCK_##i]))
#define GET_REG_N(i) ((unsigned long) (Registers[REGBLOCK_##i]))

#define SET_REG_O(i, v) ((Registers[REGBLOCK_##i]) = (v))
#define SET_REG_P(i, v) (set_ptr_register ((REGBLOCK_##i), (v)))
#define SET_REG_N(i, v) (set_ulong_register ((REGBLOCK_##i), (v)))

static inline void
set_ptr_register (unsigned int index, SCHEME_OBJECT * p)
{
  Registers[index] = (SCHEME_OBJECT) p;
}

static inline void
set_ulong_register (unsigned int index, unsigned long value)
{
  Registers[index] = (SCHEME_OBJECT) value;
}

#define GET_MEMTOP		GET_REG_P (MEMTOP)
#define GET_INT_MASK		GET_REG_N (INT_MASK)
#define GET_CC_VAL		GET_REG_O (CC_VAL)
#define GET_CC_TEMP		GET_REG_O (CC_TEMP)
#define GET_CLOSURE_FREE	GET_REG_P (CLOSURE_FREE)
#define GET_CLOSURE_SPACE	GET_REG_P (CLOSURE_SPACE)
#define GET_STACK_GUARD		GET_REG_P (STACK_GUARD)
#define GET_INT_CODE		GET_REG_N (INT_CODE)
#define GET_REFLECTOR		GET_REG_O (REFLECT_TO_INTERFACE)

#define SET_MEMTOP(v)		SET_REG_P (MEMTOP, v)
#define SET_INT_MASK(v)		SET_REG_N (INT_MASK, v)
#define SET_CC_VAL(v)		SET_REG_O (CC_VAL, v)
#define SET_CC_TEMP(v)		SET_REG_O (CC_TEMP, v)
#define SET_CLOSURE_FREE(v)	SET_REG_P (CLOSURE_FREE, v)
#define SET_CLOSURE_SPACE(v)	SET_REG_P (CLOSURE_SPACE, v)
#define SET_STACK_GUARD(v)	SET_REG_P (STACK_GUARD, v)
#define SET_INT_CODE(v)		SET_REG_N (INT_CODE, v)
#define SET_REFLECTOR(v)	SET_REG_O (REFLECT_TO_INTERFACE, v)

#endif // SCM_REGISTERS_H
