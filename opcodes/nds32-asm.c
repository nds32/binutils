/* Assembler interface for targets using CGEN. -*- C -*-
   CGEN: Cpu tools GENerator

   THIS FILE IS MACHINE GENERATED WITH CGEN.
   - the resultant file is machine generated, cgen-asm.in isn't

   Copyright 1996, 1997, 1998, 1999, 2000, 2001, 2005, 2007, 2008, 2010
   Free Software Foundation, Inc.

   This file is part of libopcodes.

   This library is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   It is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
   or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
   License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software Foundation, Inc.,
   51 Franklin Street - Fifth Floor, Boston, MA 02110-1301, USA.  */


/* ??? Eventually more and more of this stuff can go to cpu-independent files.
   Keep that in mind.  */

#include "sysdep.h"
#include <stdio.h>
#include "ansidecl.h"
#include "bfd.h"
#include "symcat.h"
#include "nds32-desc.h"
#include "nds32-opc.h"
#include "opintl.h"
#include "xregex.h"
#include "libiberty.h"
#include "safe-ctype.h"

#undef  min
#define min(a,b) ((a) < (b) ? (a) : (b))
#undef  max
#define max(a,b) ((a) > (b) ? (a) : (b))

static const char * parse_insn_normal
  (CGEN_CPU_DESC, const CGEN_INSN *, const char **, CGEN_FIELDS *);

/* -- assembler routines inserted here.  */

/* -- asm.c */

#include <ctype.h>

static const char *MISSING_CLOSING_PARENTHESIS = N_("missing `)'");

/* Handle '#' prefixes (i.e. skip over them).  */

static const char *
parse_hash (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED, const char **strp,
	    int opindex ATTRIBUTE_UNUSED, long *valuep ATTRIBUTE_UNUSED)
{
    if (**strp == '#')
	++*strp;
    return NULL;
}

#define INVALID_IMMEDIATE_SPECIFICATION "Invalid immediate specified."

static const char *
parse_unsigned_immediate (CGEN_CPU_DESC cd, const char **strp, int opindex,
			  unsigned long *valuep)
{
  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* A simple test to disable acceptance of register names as immediate.  */
  if (ISALPHA (**strp) || **strp == '$')
    return INVALID_IMMEDIATE_SPECIFICATION;
  else
    return cgen_parse_unsigned_integer (cd, strp, opindex, valuep);
}

static const char *
nds32_parse_signed_integer (CGEN_CPU_DESC cd, const char **strp,
			    int opindex, long *valuep, int nbits)
{
  /* A simple test to disable acceptance of register names as immediate.  */
  if (**strp == '$')
    return INVALID_IMMEDIATE_SPECIFICATION;
  else
    {
      bfd_vma value;
      enum cgen_parse_operand_result result;
      const char *errmsg;

      errmsg = (*cd->parse_operand_fn)
	(cd, CGEN_PARSE_OPERAND_INTEGER, strp, opindex, BFD_RELOC_NONE,
	 &result, &value);
      /* Examine `result'.  */
      if (!errmsg)
	{
	  *valuep = value;
	  if (*valuep & 0x80000000)
	    *valuep |= (long) -1 << 31;

	  if (result == CGEN_PARSE_OPERAND_RESULT_QUEUED)
	    errmsg = _("big number out of range");
	  else if (result == CGEN_PARSE_OPERAND_RESULT_REGISTER)
	    errmsg = _("immediate value expected - not register");
	  else
	    {
	      if (*valuep >= (1 << nbits) || *valuep < -(1 << nbits))
		errmsg = _("number out of range");
	    }
	}

      return errmsg;
    }
}

static const char *
nds32_parse_unsigned_integer (CGEN_CPU_DESC cd, const char **strp,
			      int opindex, unsigned long *valuep,
			      int nbits)
{
  /* A simple test to disable acceptance of register names as immediate.  */
  if (**strp == '$')
    return INVALID_IMMEDIATE_SPECIFICATION;
  else
    {
      bfd_vma value;
      enum cgen_parse_operand_result result;
      const char *errmsg;

      errmsg = (*cd->parse_operand_fn)
	(cd, CGEN_PARSE_OPERAND_INTEGER, strp, opindex, BFD_RELOC_NONE,
	 &result, &value);
      /* Examine `result'.  */
      if (!errmsg)
	{
	  *valuep = value;
	  if (result == CGEN_PARSE_OPERAND_RESULT_QUEUED)
	    errmsg = _("big number out of range");
	  else if (result == CGEN_PARSE_OPERAND_RESULT_REGISTER)
	    errmsg = _("immediate value expected - not register");
	  else
	    {
	      if ((*valuep >> nbits) > 0)
		errmsg = _("number out of range");
	    }
	}

      return errmsg;
    }
}

/* This function handles PC-relative address.  */

static const char *
parse_nds32_address (CGEN_CPU_DESC cd, const char **strp, int opindex,
		     long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  errmsg = cgen_parse_address (cd, strp, opindex, 0, &result_type, &value);

  if (result_type == CGEN_PARSE_OPERAND_RESULT_REGISTER
      || result_type == CGEN_PARSE_OPERAND_RESULT_ERROR)
    {
      errmsg = _("immediate value expected - "
		 "possibly use register as immediate value");
    }
  else
    {
      *valuep = value;
    }

  return errmsg;
}


static const char *
nds32_parse_trunc_signed_integer (CGEN_CPU_DESC cd, const char **strp,
				  int opindex, long *valuep, int nbits)
{
  /* A simple test to disable acceptance of register names as immediate.  */
  if (**strp == '$')
    return INVALID_IMMEDIATE_SPECIFICATION;
  else
    {
      bfd_vma value;
      enum cgen_parse_operand_result result;
      const char *errmsg;

      errmsg = (*cd->parse_operand_fn)
	(cd, CGEN_PARSE_OPERAND_INTEGER, strp, opindex, BFD_RELOC_NONE,
	 &result, &value);
      /* Examine `result'.  */
      if (!errmsg)
	{
	  *valuep = value;
	  if (result == CGEN_PARSE_OPERAND_RESULT_QUEUED)
	    errmsg = _("big number out of range");
	  else if (result == CGEN_PARSE_OPERAND_RESULT_REGISTER)
	    errmsg = _("immediate value expected - not register");
	  else
	    {
	      if (*valuep >= (1 << nbits) || *valuep < -(1 << nbits))
		{
		  errmsg = _("number out of range");
		}
	    }
	  *valuep &= ((1 << (nbits + 1)) - 1);
	}

      return errmsg;
    }
}

/* This function handles hi20(). This part is simple - it just extracts
   the high 20 bits.  */

static const char *
parse_uhi20 (CGEN_CPU_DESC cd, const char **strp, int opindex,
	     unsigned long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using hi20().  */
  if (strncasecmp (*strp, "hi20(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_HI20,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	{
	  value >>= 12;
	  value &= 0xfffff;
	}
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_unsigned_integer (cd, strp, opindex, valuep, 20);
}

/* This function handles lo20(). This part is simple - it just extracts the
   sign extended low 20 bits.  */

static const char *
parse_slo20 (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo20().  */
  if (strncasecmp (*strp, "lo20(", 5) == 0)
    {
      long svalue;

      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_20,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;

      ++*strp;
      *(unsigned long *) &svalue = value;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	svalue = (svalue << 12) >> 12;
      *valuep = svalue;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 19);
}

/* This function handles lo12(). This part is not simple. If lo12() is
   found, it just extracts the low 12 bits and check used in what kind
   of instruction: li or la -
        should be translated into sethi and ori instruction pair
   {ls}b{i}{.p} or {l}bs{i}{.p} -
        should be translated into sethi and load/store instruction pair
   Otherwise, it is treated as an signed integer.  */

static const char *
parse_slo19 (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using sda().  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA19S0,
				   NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* jasonwu, for lbi.gp: if user is using symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.')
    {
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA19S0,
				   NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 18);
}


/* This function handles lo12(). This part is not simple. If lo12() is
   found, it just extracts the low 12 bits and check used in what kind
   of instruction: li or la -
        should be translated into sethi and ori instruction pair
   {ls}h{i}{.p} or {l}hs{i}{.p} -
        should be translated into sethi and load/store instruction pair
   Otherwise, it is treated as an signed integer.  */

static const char *
parse_slo18h (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result;
  bfd_vma value;

  /* Ignore leading #  */
  if (**strp == '#')
    ++*strp;

  /* If user is using sda().  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA18S1,
				   NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* jasonwu, for lbi.gp: if user is using symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.')
    {
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA18S1,
				   NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 17 + 1);
}

/* This function handles lo12(). This part is not simple. If lo12() is
   found, it just extracts the low 12 bits and check used in what kind
   of instruction: li or la -
        should be translated into sethi and ori instruction pair
   {ls}w{i}{.p} -
        should be translated into sethi and load/store instruction pair.
   Otherwise, it is treated as an signed integer.  */

static const char *
parse_slo17w (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using sda().  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA17S2,
				   NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* jasonwu, for lbi.gp: if user is using symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.')
    {
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA17S2,
				   NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 16 + 2);
}

/* This function handles lo12(). This part is not simple. If lo12() is
   found, it just extracts the low 12 bits and check used in what kind
   of instruction: li or la -
        should be translated into sethi and ori instruction pair
   {ls}w{i}{.p} -
        should be translated into sethi and load/store instruction pair.
   Otherwise, it is treated as an unsigned integer.  */

static const char *
parse_ulo15d (CGEN_CPU_DESC cd, const char **strp, int opindex,
	      unsigned long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S3,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_unsigned_integer (cd, strp, opindex, valuep, 15 + 3);
}

/* This function handles lo12(). This part is not simple. If lo12() is found,
   it just extracts the low 12 bits and check used in what kind of instruction:
   li or la -
        should be translated into sethi and ori instruction pair
   {ls}w{i}{.p} -
        should be translated into sethi and load/store instruction pair.
   Otherwise, it is treated as an signed integer.  */

static const char *
parse_slo15d (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S3,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  /* If user is using sda(); NOTE: we can't support sda(sym) + addend yet.  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA15S3,
				   NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* If user is using other symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.')
    {
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA15S3,
				   NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 14 + 3);
}

/* This function handles lo12(). This part is not simple. If lo12() is found,
   it just extracts the low 12 bits and check used in what kind of instruction:
   li or la -
        should be translated into sethi and ori instruction pair
   {ls}w{i}{.p} -
        should be translated into sethi and load/store instruction pair.
   Otherwise, it is treated as an unsigned integer.  */

static const char *
parse_ulo15w (CGEN_CPU_DESC cd, const char **strp, int opindex,
	      unsigned long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S2,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_unsigned_integer (cd, strp, opindex, valuep, 15 + 2);
}

/* This function handles lo12(). This part is not simple. If lo12() is found,
   it just extracts the low 12 bits and check used in what kind of instruction:
   li or la -
        should be translated into sethi and ori instruction pair
   {ls}w{i}{.p} -
        should be translated into sethi and load/store instruction pair.
   Otherwise, it is treated as an signed integer.  */

static const char *
parse_slo15w (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S2,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  /* If user is using sda().  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA15S2,
				   NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* If user is using other symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.')
    {
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA15S2,
				   NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 14 + 2);
}

/* It just extracts the sign extended low 12 bits.  */

static const char *
parse_slo12w (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg =
	cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S2_SP,
			    &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  /* If user is using sda().  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg =
	cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA12S2_SP,
			    NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* If user is using other symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.' || **strp == '$')
    {
      errmsg =
	cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA12S2_SP,
			    NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 11 + 2);
}


/* It just extracts the sign extended low 12 bits.  */

static const char *
parse_slo12d (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex,
				   BFD_RELOC_NDS32_LO12S2_DP,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  /* If user is using sda().  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg =
	cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA12S2_DP,
			    NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* If user is using other symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.' || **strp == '$')
    {
      errmsg =
	cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA12S2_DP,
			    NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 11 + 2);
}


/* This function handles lo12(). This part is not simple. If lo12() is found,
   it just extracts the low 12 bits and check used in what kind of instruction:
   li or la -
        should be translated into sethi and ori instruction pair
   {ls}h{i}{.p} or {l}hs{i}{.p} -
        should be translated into sethi and load/store instruction pair
   Otherwise, it is treated as an unsigned integer.  */

static const char *
parse_ulo15h (CGEN_CPU_DESC cd,
	      const char **strp, int opindex, unsigned long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S1,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_unsigned_integer (cd, strp, opindex, valuep, 15 + 1);
}

/* This function handles lo12(). This part is not simple. If lo12() is found,
   it just extracts the low 12 bits and check used in what kind of instruction:
   li or la -
        should be translated into sethi and ori instruction pair
   {ls}h{i}{.p} or {l}hs{i}{.p} -
        should be translated into sethi and load/store instruction pair
   Otherwise, it is treated as an signed integer.  */

static const char *
parse_slo15h (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S1,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  /* If user is using sda().  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA15S1,
				   NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* If user is using other symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.')
    {
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA15S1,
				   NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 14 + 1);
}

/* This function handles lo12(). This part is not simple. If lo12() is
   found, it just extracts the low 12 bits and check used in what kind
   of instruction: li or la -
        should be translated into sethi and ori instruction pair
   {ls}b{i}{.p} or {l}bs{i}{.p} -
        should be translated into sethi and load/store instruction pair
   Otherwise, it is treated as an unsigned integer.  */

static const char *
parse_ulo15 (CGEN_CPU_DESC cd,
	     const char **strp, int opindex, unsigned long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S0,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_unsigned_integer (cd, strp, opindex, valuep, 15);
}

/* This function handles lo12(). This part is not simple. If lo12() is
   found, it just extracts the low 12 bits and check used in what kind
   of instruction: li or la -
        should be translated into sethi and ori instruction pair
   {ls}b{i}{.p} or {l}bs{i}{.p} -
        should be translated into sethi and load/store instruction pair
   Otherwise, it is treated as an signed integer.  */

static const char *
parse_slo15 (CGEN_CPU_DESC cd, const char **strp, int opindex, long *valuep)
{
  const char *errmsg;
  enum cgen_parse_operand_result result_type;
  bfd_vma value;

  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* If user is using lo12().  */
  if (strncasecmp (*strp, "lo12(", 5) == 0)
    {
      *strp += 5;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_LO12S0,
				   &result_type, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      if (errmsg == NULL && result_type == CGEN_PARSE_OPERAND_RESULT_NUMBER)
	value &= 0xfff;
      *valuep = value;
      return errmsg;
    }

  /* If user is using sda().  */
  if (strncasecmp (*strp, "sda(", 4) == 0)
    {
      *strp += 4;
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA15S0,
				   NULL, &value);
      if (**strp != ')')
	return MISSING_CLOSING_PARENTHESIS;
      ++*strp;
      *valuep = value;
      return errmsg;
    }

  /* If user is using other symbol.  */
  if (ISALPHA (**strp) || **strp == '_' || **strp == '.')
    {
      errmsg = cgen_parse_address (cd, strp, opindex, BFD_RELOC_NDS32_SDA15S0,
				   NULL, &value);
      *valuep = value;
      return errmsg;
    }

  return nds32_parse_signed_integer (cd, strp, opindex, valuep, 14);
}

/* This function treats the 16-bit immediate as unsigned/signed number
   for AMTARI instruction of audio extension.  */

static const char *
parse_imm16_a (CGEN_CPU_DESC cd, const char **strp, int opindex,
	       unsigned long *valuep)
{
  /* Ignore leading #.  */
  if (**strp == '#')
    ++*strp;

  /* A simple test to disable acceptance of register names as immediate.  */
  if ((*(*strp - 3) == 'm') && (*(*strp + 1) != 'x'))
    return nds32_parse_trunc_signed_integer (cd, strp, opindex,
					     (long *) valuep, 15);
  else
    return nds32_parse_unsigned_integer (cd, strp, opindex, valuep, 16);
}

static const char *
nds32_parse_insn_mov55 (CGEN_CPU_DESC cd, const CGEN_INSN *insn,
			const char **strp, CGEN_FIELDS *fields)
{
  const char *msg;

  msg = parse_insn_normal (cd, insn, strp, fields);
  if (msg)
    return msg;

  /* At-least v3 and rt == ra == $sp.
     It is ifret16 in V3.  */
  if ((cd->machs >> MACH_N1H_V3)
      && (fields->f_16_rt5h == fields->f_16_ra5h) && fields->f_16_rt5h == 31)
    return "rt == $sp and ra == $sp is not allowed in V3.";
  return NULL;
}

/* -- dis.c */

const char * nds32_cgen_parse_operand
  (CGEN_CPU_DESC, int, const char **, CGEN_FIELDS *);

/* Main entry point for operand parsing.

   This function is basically just a big switch statement.  Earlier versions
   used tables to look up the function to use, but
   - if the table contains both assembler and disassembler functions then
     the disassembler contains much of the assembler and vice-versa,
   - there's a lot of inlining possibilities as things grow,
   - using a switch statement avoids the function call overhead.

   This function could be moved into `parse_insn_normal', but keeping it
   separate makes clear the interface between `parse_insn_normal' and each of
   the handlers.  */

const char *
nds32_cgen_parse_operand (CGEN_CPU_DESC cd,
			   int opindex,
			   const char ** strp,
			   CGEN_FIELDS * fields)
{
  const char * errmsg = NULL;
  /* Used by scalar operands that still need to be parsed.  */
  long junk ATTRIBUTE_UNUSED;

  switch (opindex)
    {
    case NDS32_OPERAND_AR2IDX5_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ai_ar2idx5, & fields->f_32_aridx5_a);
      break;
    case NDS32_OPERAND_ARIDX4_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ai_aridx4, & fields->f_32_aridx4_a);
      break;
    case NDS32_OPERAND_ARIDX5_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ai_aridx5, & fields->f_32_aridx5_a);
      break;
    case NDS32_OPERAND_BITS :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_xlsb, & fields->f_16_uimm3);
      break;
    case NDS32_OPERAND_C1_15_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_C1_15_A, (unsigned long *) (& fields->f_32_c1_15_a));
      break;
    case NDS32_OPERAND_CCTLLVL :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_cctllvl, & fields->f_32tx_1_21);
      break;
    case NDS32_OPERAND_CCTLST :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_cctlst, & fields->f_32t4_ext5);
      break;
    case NDS32_OPERAND_CONCAT24 :
      errmsg = parse_nds32_address (cd, strp, NDS32_OPERAND_CONCAT24, (long *) (& fields->f_32_concat24));
      break;
    case NDS32_OPERAND_COPDR :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_cpr_names, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_COPWR :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_cpr_names, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_CPID :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_CPID, (unsigned long *) (& fields->f_32_2_26));
      break;
    case NDS32_OPERAND_CPID2 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_CPID2, (unsigned long *) (& fields->f_32tx_2_17));
      break;
    case NDS32_OPERAND_D1_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ar_accum, & fields->f_32_d1_a);
      break;
    case NDS32_OPERAND_DH2_16_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ar_accum1, & fields->f_32_dh2_16_a);
      break;
    case NDS32_OPERAND_DH2_6_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_accum_hl_names, & fields->f_32_dh2_6_a);
      break;
    case NDS32_OPERAND_DISP14 :
      errmsg = parse_nds32_address (cd, strp, NDS32_OPERAND_DISP14, (long *) (& fields->f_32t2_disp14));
      break;
    case NDS32_OPERAND_DISP16 :
      errmsg = parse_nds32_address (cd, strp, NDS32_OPERAND_DISP16, (long *) (& fields->f_32t1_disp16));
      break;
    case NDS32_OPERAND_DISP24 :
      errmsg = parse_nds32_address (cd, strp, NDS32_OPERAND_DISP24, (long *) (& fields->f_32t0_disp24));
      break;
    case NDS32_OPERAND_DISP8 :
      errmsg = parse_nds32_address (cd, strp, NDS32_OPERAND_DISP8, (long *) (& fields->f_32t1_disp8));
      break;
    case NDS32_OPERAND_DISP9 :
      errmsg = parse_nds32_address (cd, strp, NDS32_OPERAND_DISP9, (long *) (& fields->f_32t1_disp9));
      break;
    case NDS32_OPERAND_DPREFST :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_dprefst, & fields->f_32t2_st4);
      break;
    case NDS32_OPERAND_FDRA5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_fdr, & fields->f_32_ra5);
      break;
    case NDS32_OPERAND_FDRB5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_fdr, & fields->f_32_rb5);
      break;
    case NDS32_OPERAND_FDRT5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_fdr, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_FSRA5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_fsr_names, & fields->f_32_ra5);
      break;
    case NDS32_OPERAND_FSRB5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_fsr_names, & fields->f_32_rb5);
      break;
    case NDS32_OPERAND_FSRT5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_fsr_names, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_GROUPIDX :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_GROUPIDX, (unsigned long *) (& fields->f_32_group));
      break;
    case NDS32_OPERAND_HASH :
      errmsg = parse_hash (cd, strp, NDS32_OPERAND_HASH, (long *) (& junk));
      break;
    case NDS32_OPERAND_HSDISP8 :
      errmsg = parse_nds32_address (cd, strp, NDS32_OPERAND_HSDISP8, (long *) (& fields->f_16_hsdisp8));
      break;
    case NDS32_OPERAND_I2_1_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_I2_1_A, (unsigned long *) (& fields->f_32_i2_1_a));
      break;
    case NDS32_OPERAND_IM1_4_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_IM1_4_A, (unsigned long *) (& fields->f_32_im1_4_a));
      break;
    case NDS32_OPERAND_IM5_I_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ar_i, & fields->f_32_im5_i_a);
      break;
    case NDS32_OPERAND_IM5_M_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ar_m, & fields->f_32_im5_m_a);
      break;
    case NDS32_OPERAND_IM6_I_0_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ar_i_lo, & fields->f_32_im6_i_0_a);
      break;
    case NDS32_OPERAND_IM6_I_1_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ar_i_hi, & fields->f_32_im6_i_1_a);
      break;
    case NDS32_OPERAND_IM6_M_0_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ar_m_lo, & fields->f_32_im6_m_0_a);
      break;
    case NDS32_OPERAND_IM6_M_1_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_ar_m_hi, & fields->f_32_im6_m_1_a);
      break;
    case NDS32_OPERAND_IMM16_A :
      errmsg = parse_imm16_a (cd, strp, NDS32_OPERAND_IMM16_A, (unsigned long *) (& fields->f_32_imm16_a));
      break;
    case NDS32_OPERAND_IMM5U :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_IMM5U, (unsigned long *) (& fields->f_16_uimm5));
      break;
    case NDS32_OPERAND_LSBLOC_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_LSBLOC_A, (unsigned long *) (& fields->f_32_lsbloc_a));
      break;
    case NDS32_OPERAND_M2_3_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_M2_3_A, (unsigned long *) (& fields->f_32_m2_3_a));
      break;
    case NDS32_OPERAND_M2_5_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_M2_5_A, (unsigned long *) (& fields->f_32_m2_5_a));
      break;
    case NDS32_OPERAND_MASK4 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_MASK4, (unsigned long *) (& fields->f_32t5_mask4));
      break;
    case NDS32_OPERAND_MFUSRIDX :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_mfusridx, & fields->f_32_group_usr);
      break;
    case NDS32_OPERAND_MSYNCST :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_msyncst, & fields->f_32t3_ext3);
      break;
    case NDS32_OPERAND_MTUSRIDX :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_mtusridx, & fields->f_32_group_usr);
      break;
    case NDS32_OPERAND_R10A5_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo, & fields->f_32_r10a5_a);
      break;
    case NDS32_OPERAND_R10A5_A_B :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo_bottom, & fields->f_32_r10a5_a);
      break;
    case NDS32_OPERAND_R10A5_A_T :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo_top, & fields->f_32_r10a5_a);
      break;
    case NDS32_OPERAND_R10B5_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo, & fields->f_32_r10b5_a);
      break;
    case NDS32_OPERAND_R10B5_A_B :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo_bottom, & fields->f_32_r10b5_a);
      break;
    case NDS32_OPERAND_R10B5_A_T :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo_top, & fields->f_32_r10b5_a);
      break;
    case NDS32_OPERAND_R10C5_0_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo_even, & fields->f_32_r10c5_0_a);
      break;
    case NDS32_OPERAND_R10C5_1_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo_odd, & fields->f_32_r10c5_1_a);
      break;
    case NDS32_OPERAND_R10C5_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_lo, & fields->f_32_r10c5_a);
      break;
    case NDS32_OPERAND_RA3 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names_8, & fields->f_16_ra3);
      break;
    case NDS32_OPERAND_RA4 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names_16, & fields->f_16_ra4);
      break;
    case NDS32_OPERAND_RA4_19_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_RA4_19_A, (unsigned long *) (& fields->f_32_ra4_19_a));
      break;
    case NDS32_OPERAND_RA5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_ra5);
      break;
    case NDS32_OPERAND_RA5_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_ra5_a);
      break;
    case NDS32_OPERAND_RA5_A_B :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_ra5_a);
      break;
    case NDS32_OPERAND_RA5_A_T :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_ra5_a);
      break;
    case NDS32_OPERAND_RA5E :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_even_gr_names_16, & fields->f_16_ra5e);
      break;
    case NDS32_OPERAND_RA5H :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_16_ra5h);
      break;
    case NDS32_OPERAND_RB3 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names_8, & fields->f_16_rb3);
      break;
    case NDS32_OPERAND_RB3_14_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_RB3_14_A, (unsigned long *) (& fields->f_32_rb3_14_a));
      break;
    case NDS32_OPERAND_RB5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rb5);
      break;
    case NDS32_OPERAND_RB5_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rb5_a);
      break;
    case NDS32_OPERAND_RB5_A_B :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rb5_a);
      break;
    case NDS32_OPERAND_RB5_A_T :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rb5_a);
      break;
    case NDS32_OPERAND_RB5H :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_16_rb5h);
      break;
    case NDS32_OPERAND_RB5P_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rb5p_a);
      break;
    case NDS32_OPERAND_RB5P_A_B :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rb5p_a);
      break;
    case NDS32_OPERAND_RB5P_A_T :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rb5p_a);
      break;
    case NDS32_OPERAND_RC1_5_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_RC1_5_A, (unsigned long *) (& fields->f_32_rc1_5_a));
      break;
    case NDS32_OPERAND_RC2_11_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_RC2_11_A, (unsigned long *) (& fields->f_32_rc2_11_a));
      break;
    case NDS32_OPERAND_RC4_A :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_RC4_A, (unsigned long *) (& fields->f_32_rc4_a));
      break;
    case NDS32_OPERAND_RC5_0_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_even, & fields->f_32_rc5_0_a);
      break;
    case NDS32_OPERAND_RC5_1_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_gr_odd, & fields->f_32_rc5_1_a);
      break;
    case NDS32_OPERAND_RD1 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_accum_names, & fields->f_32_rd1);
      break;
    case NDS32_OPERAND_RD1HL :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_accum_hl_names, & fields->f_32_rd1hl);
      break;
    case NDS32_OPERAND_RD5_A :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rd5_a);
      break;
    case NDS32_OPERAND_REGLIST :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_reglist, & fields->f_16_mask2);
      break;
    case NDS32_OPERAND_RS5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rs5);
      break;
    case NDS32_OPERAND_RT3 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names_8, & fields->f_16_rt3);
      break;
    case NDS32_OPERAND_RT3_7 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names_8, & fields->f_16_rt3_7);
      break;
    case NDS32_OPERAND_RT3E5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names_8e5, & fields->f_16_rt3);
      break;
    case NDS32_OPERAND_RT4 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names_16, & fields->f_16_rt4);
      break;
    case NDS32_OPERAND_RT5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_RT5E :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_even_gr_names_16, & fields->f_16_rt5e);
      break;
    case NDS32_OPERAND_RT5H :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_16_rt5h);
      break;
    case NDS32_OPERAND_RTH5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_RTL5 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_gr_names, & fields->f_32_ra5);
      break;
    case NDS32_OPERAND_SI :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_SI, (unsigned long *) (& fields->f_32t3_sub10si));
      break;
    case NDS32_OPERAND_SIMM10 :
      errmsg = parse_slo20 (cd, strp, NDS32_OPERAND_SIMM10, (long *) (& fields->f_16_simm10));
      break;
    case NDS32_OPERAND_SIMM11 :
      errmsg = parse_slo15 (cd, strp, NDS32_OPERAND_SIMM11, (long *) (& fields->f_32t2_simm11));
      break;
    case NDS32_OPERAND_SIMM5H :
      errmsg = parse_slo20 (cd, strp, NDS32_OPERAND_SIMM5H, (long *) (& fields->f_16_simm5));
      break;
    case NDS32_OPERAND_SIMM5W :
      errmsg = parse_slo20 (cd, strp, NDS32_OPERAND_SIMM5W, (long *) (& fields->f_16_simm5w));
      break;
    case NDS32_OPERAND_SLO12D :
      errmsg = parse_slo12d (cd, strp, NDS32_OPERAND_SLO12D, (long *) (& fields->f_32tx_slo12d));
      break;
    case NDS32_OPERAND_SLO12W :
      errmsg = parse_slo12w (cd, strp, NDS32_OPERAND_SLO12W, (long *) (& fields->f_32tx_slo12w));
      break;
    case NDS32_OPERAND_SLO15 :
      errmsg = parse_slo15 (cd, strp, NDS32_OPERAND_SLO15, (long *) (& fields->f_32t2_slo15b));
      break;
    case NDS32_OPERAND_SLO15B :
      errmsg = parse_slo15 (cd, strp, NDS32_OPERAND_SLO15B, (long *) (& fields->f_32t2_slo15b));
      break;
    case NDS32_OPERAND_SLO15D :
      errmsg = parse_slo15d (cd, strp, NDS32_OPERAND_SLO15D, (long *) (& fields->f_32t2_slo15d));
      break;
    case NDS32_OPERAND_SLO15H :
      errmsg = parse_slo15h (cd, strp, NDS32_OPERAND_SLO15H, (long *) (& fields->f_32t2_slo15h));
      break;
    case NDS32_OPERAND_SLO15W :
      errmsg = parse_slo15w (cd, strp, NDS32_OPERAND_SLO15W, (long *) (& fields->f_32t2_slo15w));
      break;
    case NDS32_OPERAND_SLO17W :
      errmsg = parse_slo17w (cd, strp, NDS32_OPERAND_SLO17W, (long *) (& fields->f_32_slo17w));
      break;
    case NDS32_OPERAND_SLO18H :
      errmsg = parse_slo18h (cd, strp, NDS32_OPERAND_SLO18H, (long *) (& fields->f_32_slo18h));
      break;
    case NDS32_OPERAND_SLO19 :
      errmsg = parse_slo19 (cd, strp, NDS32_OPERAND_SLO19, (long *) (& fields->f_32_slo19));
      break;
    case NDS32_OPERAND_SLO20 :
      errmsg = parse_slo20 (cd, strp, NDS32_OPERAND_SLO20, (long *) (& fields->f_32t1_slo20));
      break;
    case NDS32_OPERAND_SR10 :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_sr_names, & fields->f_32_sr10);
      break;
    case NDS32_OPERAND_STANDBYST :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_standbyst, & fields->f_32t4_ext2);
      break;
    case NDS32_OPERAND_SUIMM5 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_SUIMM5, (unsigned long *) (& fields->f_16_suimm5));
      break;
    case NDS32_OPERAND_SWID15 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_SWID15, (unsigned long *) (& fields->f_32t3_swid15));
      break;
    case NDS32_OPERAND_SWID5 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_SWID5, (unsigned long *) (& fields->f_16_swid5));
      break;
    case NDS32_OPERAND_SWID9 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_SWID9, (unsigned long *) (& fields->f_16_swid9));
      break;
    case NDS32_OPERAND_TLBOPST :
      errmsg = cgen_parse_keyword (cd, strp, & nds32_cgen_opval_h_tlbopst, & fields->f_32t4_ext5);
      break;
    case NDS32_OPERAND_UHI20 :
      errmsg = parse_uhi20 (cd, strp, NDS32_OPERAND_UHI20, (unsigned long *) (& fields->f_32t1_uhi20));
      break;
    case NDS32_OPERAND_UIMM12 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM12, (unsigned long *) (& fields->f_32_12_12));
      break;
    case NDS32_OPERAND_UIMM19 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM19, (unsigned long *) (& fields->f_32_19_7));
      break;
    case NDS32_OPERAND_UIMM3 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM3, (unsigned long *) (& fields->f_16_uimm3));
      break;
    case NDS32_OPERAND_UIMM3_10 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM3_10, (unsigned long *) (& fields->f_16_uimm3_10));
      break;
    case NDS32_OPERAND_UIMM5 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM5, (unsigned long *) (& fields->f_32t3_uimm5));
      break;
    case NDS32_OPERAND_UIMM5D :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM5D, (unsigned long *) (& fields->f_16_uimm5d));
      break;
    case NDS32_OPERAND_UIMM5H :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM5H, (unsigned long *) (& fields->f_16_uimm5));
      break;
    case NDS32_OPERAND_UIMM6W :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM6W, (unsigned long *) (& fields->f_16_uimm6w));
      break;
    case NDS32_OPERAND_UIMM8_S :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM8_S, (unsigned long *) (& fields->f_32_uimm8_s));
      break;
    case NDS32_OPERAND_UIMM_SR10 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_UIMM_SR10, (unsigned long *) (& fields->f_32_sr10));
      break;
    case NDS32_OPERAND_ULO15 :
      errmsg = parse_ulo15 (cd, strp, NDS32_OPERAND_ULO15, (unsigned long *) (& fields->f_32t2_ulo15b));
      break;
    case NDS32_OPERAND_ULO15B :
      errmsg = parse_ulo15 (cd, strp, NDS32_OPERAND_ULO15B, (unsigned long *) (& fields->f_32t2_ulo15b));
      break;
    case NDS32_OPERAND_ULO15D :
      errmsg = parse_ulo15d (cd, strp, NDS32_OPERAND_ULO15D, (unsigned long *) (& fields->f_32t2_ulo15d));
      break;
    case NDS32_OPERAND_ULO15H :
      errmsg = parse_ulo15h (cd, strp, NDS32_OPERAND_ULO15H, (unsigned long *) (& fields->f_32t2_ulo15h));
      break;
    case NDS32_OPERAND_ULO15W :
      errmsg = parse_ulo15w (cd, strp, NDS32_OPERAND_ULO15W, (unsigned long *) (& fields->f_32t2_ulo15w));
      break;
    case NDS32_OPERAND_ULO3B :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_ULO3B, (unsigned long *) (& fields->f_16_ulo3b));
      break;
    case NDS32_OPERAND_ULO3H :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_ULO3H, (unsigned long *) (& fields->f_16_ulo3h));
      break;
    case NDS32_OPERAND_ULO3W :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_ULO3W, (unsigned long *) (& fields->f_16_ulo3w));
      break;
    case NDS32_OPERAND_ULO5 :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_ULO5, (unsigned long *) (& fields->f_32t21_ulo5));
      break;
    case NDS32_OPERAND_ULO7W :
      errmsg = parse_unsigned_immediate (cd, strp, NDS32_OPERAND_ULO7W, (unsigned long *) (& fields->f_16_ulo7w));
      break;
    case NDS32_OPERAND_USRIDX :
      errmsg = cgen_parse_unsigned_integer (cd, strp, NDS32_OPERAND_USRIDX, (unsigned long *) (& fields->f_32_usr));
      break;

    default :
      /* xgettext:c-format */
      fprintf (stderr, _("Unrecognized field %d while parsing.\n"), opindex);
      abort ();
  }

  return errmsg;
}

cgen_parse_fn * const nds32_cgen_parse_handlers[] = 
{
  parse_insn_normal,
  parse_insn_special0,
};

void
nds32_cgen_init_asm (CGEN_CPU_DESC cd)
{
  nds32_cgen_init_opcode_table (cd);
  nds32_cgen_init_ibld_table (cd);
  cd->parse_handlers = & nds32_cgen_parse_handlers[0];
  cd->parse_operand = nds32_cgen_parse_operand;
#ifdef CGEN_ASM_INIT_HOOK
CGEN_ASM_INIT_HOOK
#endif
}



/* Regex construction routine.

   This translates an opcode syntax string into a regex string,
   by replacing any non-character syntax element (such as an
   opcode) with the pattern '.*'

   It then compiles the regex and stores it in the opcode, for
   later use by nds32_cgen_assemble_insn

   Returns NULL for success, an error message for failure.  */

char * 
nds32_cgen_build_insn_regex (CGEN_INSN *insn)
{  
  CGEN_OPCODE *opc = (CGEN_OPCODE *) CGEN_INSN_OPCODE (insn);
  const char *mnem = CGEN_INSN_MNEMONIC (insn);
  char rxbuf[CGEN_MAX_RX_ELEMENTS];
  char *rx = rxbuf;
  const CGEN_SYNTAX_CHAR_TYPE *syn;
  int reg_err;

  syn = CGEN_SYNTAX_STRING (CGEN_OPCODE_SYNTAX (opc));

  /* Mnemonics come first in the syntax string.  */
  if (! CGEN_SYNTAX_MNEMONIC_P (* syn))
    return _("missing mnemonic in syntax string");
  ++syn;

  /* Generate a case sensitive regular expression that emulates case
     insensitive matching in the "C" locale.  We cannot generate a case
     insensitive regular expression because in Turkish locales, 'i' and 'I'
     are not equal modulo case conversion.  */

  /* Copy the literal mnemonic out of the insn.  */
  for (; *mnem; mnem++)
    {
      char c = *mnem;

      if (ISALPHA (c))
	{
	  *rx++ = '[';
	  *rx++ = TOLOWER (c);
	  *rx++ = TOUPPER (c);
	  *rx++ = ']';
	}
      else
	*rx++ = c;
    }

  /* Copy any remaining literals from the syntax string into the rx.  */
  for(; * syn != 0 && rx <= rxbuf + (CGEN_MAX_RX_ELEMENTS - 7 - 4); ++syn)
    {
      if (CGEN_SYNTAX_CHAR_P (* syn)) 
	{
	  char c = CGEN_SYNTAX_CHAR (* syn);

	  switch (c) 
	    {
	      /* Escape any regex metacharacters in the syntax.  */
	    case '.': case '[': case '\\': 
	    case '*': case '^': case '$': 

#ifdef CGEN_ESCAPE_EXTENDED_REGEX
	    case '?': case '{': case '}': 
	    case '(': case ')': case '*':
	    case '|': case '+': case ']':
#endif
	      *rx++ = '\\';
	      *rx++ = c;
	      break;

	    default:
	      if (ISALPHA (c))
		{
		  *rx++ = '[';
		  *rx++ = TOLOWER (c);
		  *rx++ = TOUPPER (c);
		  *rx++ = ']';
		}
	      else
		*rx++ = c;
	      break;
	    }
	}
      else
	{
	  /* Replace non-syntax fields with globs.  */
	  *rx++ = '.';
	  *rx++ = '*';
	}
    }

  /* Trailing whitespace ok.  */
  * rx++ = '['; 
  * rx++ = ' '; 
  * rx++ = '\t'; 
  * rx++ = ']'; 
  * rx++ = '*'; 

  /* But anchor it after that.  */
  * rx++ = '$'; 
  * rx = '\0';

  CGEN_INSN_RX (insn) = xmalloc (sizeof (regex_t));
  reg_err = regcomp ((regex_t *) CGEN_INSN_RX (insn), rxbuf, REG_NOSUB);

  if (reg_err == 0) 
    return NULL;
  else
    {
      static char msg[80];

      regerror (reg_err, (regex_t *) CGEN_INSN_RX (insn), msg, 80);
      regfree ((regex_t *) CGEN_INSN_RX (insn));
      free (CGEN_INSN_RX (insn));
      (CGEN_INSN_RX (insn)) = NULL;
      return msg;
    }
}


/* Default insn parser.

   The syntax string is scanned and operands are parsed and stored in FIELDS.
   Relocs are queued as we go via other callbacks.

   ??? Note that this is currently an all-or-nothing parser.  If we fail to
   parse the instruction, we return 0 and the caller will start over from
   the beginning.  Backtracking will be necessary in parsing subexpressions,
   but that can be handled there.  Not handling backtracking here may get
   expensive in the case of the m68k.  Deal with later.

   Returns NULL for success, an error message for failure.  */

static const char *
parse_insn_normal (CGEN_CPU_DESC cd,
		   const CGEN_INSN *insn,
		   const char **strp,
		   CGEN_FIELDS *fields)
{
  /* ??? Runtime added insns not handled yet.  */
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  const char *str = *strp;
  const char *errmsg;
  const char *p;
  const CGEN_SYNTAX_CHAR_TYPE * syn;
#ifdef CGEN_MNEMONIC_OPERANDS
  /* FIXME: wip */
  int past_opcode_p;
#endif

  /* For now we assume the mnemonic is first (there are no leading operands).
     We can parse it without needing to set up operand parsing.
     GAS's input scrubber will ensure mnemonics are lowercase, but we may
     not be called from GAS.  */
  p = CGEN_INSN_MNEMONIC (insn);
  while (*p && TOLOWER (*p) == TOLOWER (*str))
    ++p, ++str;

  if (* p)
    return _("unrecognized instruction");

#ifndef CGEN_MNEMONIC_OPERANDS
  if (* str && ! ISSPACE (* str))
    return _("unrecognized instruction");
#endif

  CGEN_INIT_PARSE (cd);
  cgen_init_parse_operand (cd);
#ifdef CGEN_MNEMONIC_OPERANDS
  past_opcode_p = 0;
#endif

  /* We don't check for (*str != '\0') here because we want to parse
     any trailing fake arguments in the syntax string.  */
  syn = CGEN_SYNTAX_STRING (syntax);

  /* Mnemonics come first for now, ensure valid string.  */
  if (! CGEN_SYNTAX_MNEMONIC_P (* syn))
    abort ();

  ++syn;

  while (* syn != 0)
    {
      /* Non operand chars must match exactly.  */
      if (CGEN_SYNTAX_CHAR_P (* syn))
	{
	  /* FIXME: While we allow for non-GAS callers above, we assume the
	     first char after the mnemonic part is a space.  */
	  /* FIXME: We also take inappropriate advantage of the fact that
	     GAS's input scrubber will remove extraneous blanks.  */
	  if (TOLOWER (*str) == TOLOWER (CGEN_SYNTAX_CHAR (* syn)))
	    {
#ifdef CGEN_MNEMONIC_OPERANDS
	      if (CGEN_SYNTAX_CHAR(* syn) == ' ')
		past_opcode_p = 1;
#endif
	      ++ syn;
	      ++ str;
	    }
	  else if (*str)
	    {
	      /* Syntax char didn't match.  Can't be this insn.  */
	      static char msg [80];

	      /* xgettext:c-format */
	      sprintf (msg, _("syntax error (expected char `%c', found `%c')"),
		       CGEN_SYNTAX_CHAR(*syn), *str);
	      return msg;
	    }
	  else
	    {
	      /* Ran out of input.  */
	      static char msg [80];

	      /* xgettext:c-format */
	      sprintf (msg, _("syntax error (expected char `%c', found end of instruction)"),
		       CGEN_SYNTAX_CHAR(*syn));
	      return msg;
	    }
	  continue;
	}

#ifdef CGEN_MNEMONIC_OPERANDS
      (void) past_opcode_p;
#endif
      /* We have an operand of some sort.  */
      errmsg = cd->parse_operand (cd, CGEN_SYNTAX_FIELD (*syn), &str, fields);
      if (errmsg)
	return errmsg;

      /* Done with this operand, continue with next one.  */
      ++ syn;
    }

  /* If we're at the end of the syntax string, we're done.  */
  if (* syn == 0)
    {
      /* FIXME: For the moment we assume a valid `str' can only contain
	 blanks now.  IE: We needn't try again with a longer version of
	 the insn and it is assumed that longer versions of insns appear
	 before shorter ones (eg: lsr r2,r3,1 vs lsr r2,r3).  */
      while (ISSPACE (* str))
	++ str;

      if (* str != '\0')
	return _("junk at end of line"); /* FIXME: would like to include `str' */

      return NULL;
    }

  /* We couldn't parse it.  */
  return _("unrecognized instruction");
}

/* Main entry point.
   This routine is called for each instruction to be assembled.
   STR points to the insn to be assembled.
   We assume all necessary tables have been initialized.
   The assembled instruction, less any fixups, is stored in BUF.
   Remember that if CGEN_INT_INSN_P then BUF is an int and thus the value
   still needs to be converted to target byte order, otherwise BUF is an array
   of bytes in target byte order.
   The result is a pointer to the insn's entry in the opcode table,
   or NULL if an error occured (an error message will have already been
   printed).

   Note that when processing (non-alias) macro-insns,
   this function recurses.

   ??? It's possible to make this cpu-independent.
   One would have to deal with a few minor things.
   At this point in time doing so would be more of a curiosity than useful
   [for example this file isn't _that_ big], but keeping the possibility in
   mind helps keep the design clean.  */

const CGEN_INSN *
nds32_cgen_assemble_insn (CGEN_CPU_DESC cd,
			   const char *str,
			   CGEN_FIELDS *fields,
			   CGEN_INSN_BYTES_PTR buf,
			   char **errmsg)
{
  const char *start;
  CGEN_INSN_LIST *ilist;
  const char *parse_errmsg = NULL;
  const char *insert_errmsg = NULL;
  int recognized_mnemonic = 0;

  /* Skip leading white space.  */
  while (ISSPACE (* str))
    ++ str;

  /* The instructions are stored in hashed lists.
     Get the first in the list.  */
  ilist = CGEN_ASM_LOOKUP_INSN (cd, str);

  /* Keep looking until we find a match.  */
  start = str;
  for ( ; ilist != NULL ; ilist = CGEN_ASM_NEXT_INSN (ilist))
    {
      const CGEN_INSN *insn = ilist->insn;
      recognized_mnemonic = 1;

#ifdef CGEN_VALIDATE_INSN_SUPPORTED 
      /* Not usually needed as unsupported opcodes
	 shouldn't be in the hash lists.  */
      /* Is this insn supported by the selected cpu?  */
      if (! nds32_cgen_insn_supported (cd, insn))
	continue;
#endif
      /* If the RELAXED attribute is set, this is an insn that shouldn't be
	 chosen immediately.  Instead, it is used during assembler/linker
	 relaxation if possible.  */
      if (CGEN_INSN_ATTR_VALUE (insn, CGEN_INSN_RELAXED) != 0)
	continue;

      str = start;

      /* Skip this insn if str doesn't look right lexically.  */
      if (CGEN_INSN_RX (insn) != NULL &&
	  regexec ((regex_t *) CGEN_INSN_RX (insn), str, 0, NULL, 0) == REG_NOMATCH)
	continue;

      /* Allow parse/insert handlers to obtain length of insn.  */
      CGEN_FIELDS_BITSIZE (fields) = CGEN_INSN_BITSIZE (insn);

      parse_errmsg = CGEN_PARSE_FN (cd, insn) (cd, insn, & str, fields);
      if (parse_errmsg != NULL)
	continue;

      /* ??? 0 is passed for `pc'.  */
      insert_errmsg = CGEN_INSERT_FN (cd, insn) (cd, insn, fields, buf,
						 (bfd_vma) 0);
      if (insert_errmsg != NULL)
        continue;

      /* It is up to the caller to actually output the insn and any
         queued relocs.  */
      return insn;
    }

  {
    static char errbuf[150];
    const char *tmp_errmsg;
#ifdef CGEN_VERBOSE_ASSEMBLER_ERRORS
#define be_verbose 1
#else
#define be_verbose 0
#endif

    if (be_verbose)
      {
	/* If requesting verbose error messages, use insert_errmsg.
	   Failing that, use parse_errmsg.  */
	tmp_errmsg = (insert_errmsg ? insert_errmsg :
		      parse_errmsg ? parse_errmsg :
		      recognized_mnemonic ?
		      _("unrecognized form of instruction") :
		      _("unrecognized instruction"));

	if (strlen (start) > 50)
	  /* xgettext:c-format */
	  sprintf (errbuf, "%s `%.50s...'", tmp_errmsg, start);
	else 
	  /* xgettext:c-format */
	  sprintf (errbuf, "%s `%.50s'", tmp_errmsg, start);
      }
    else
      {
	if (strlen (start) > 50)
	  /* xgettext:c-format */
	  sprintf (errbuf, _("bad instruction `%.50s...'"), start);
	else 
	  /* xgettext:c-format */
	  sprintf (errbuf, _("bad instruction `%.50s'"), start);
      }
      
    *errmsg = errbuf;
    return NULL;
  }
}
