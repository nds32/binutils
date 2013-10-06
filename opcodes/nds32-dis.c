/* Disassembler interface for targets using CGEN. -*- C -*-
   CGEN: Cpu tools GENerator

   THIS FILE IS MACHINE GENERATED WITH CGEN.
   - the resultant file is machine generated, cgen-dis.in isn't

   Copyright 1996, 1997, 1998, 1999, 2000, 2001, 2002, 2003, 2005, 2007,
   2008, 2010  Free Software Foundation, Inc.

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
#include "dis-asm.h"
#include "bfd.h"
#include "symcat.h"
#include "libiberty.h"
#include "nds32-desc.h"
#include "nds32-opc.h"
#include "opintl.h"

/* Default text to print if an instruction isn't recognized.  */
#define UNKNOWN_INSN_MSG _("*unknown*")

static void print_normal
  (CGEN_CPU_DESC, void *, long, unsigned int, bfd_vma, int);
static void print_address
  (CGEN_CPU_DESC, void *, bfd_vma, unsigned int, bfd_vma, int) ATTRIBUTE_UNUSED;
static void print_keyword
  (CGEN_CPU_DESC, void *, CGEN_KEYWORD *, long, unsigned int) ATTRIBUTE_UNUSED;
static void print_insn_normal
  (CGEN_CPU_DESC, void *, const CGEN_INSN *, CGEN_FIELDS *, bfd_vma, int);
static int print_insn
  (CGEN_CPU_DESC, bfd_vma,  disassemble_info *, bfd_byte *, unsigned);
static int default_print_insn
  (CGEN_CPU_DESC, bfd_vma, disassemble_info *) ATTRIBUTE_UNUSED;
static int read_insn
  (CGEN_CPU_DESC, bfd_vma, disassemble_info *, bfd_byte *, int, CGEN_EXTRACT_INFO *,
   unsigned long *);

/* -- disassembler routines inserted here.  */

/* -- dis.c */
int nds32_cgen_get_int_operand (CGEN_CPU_DESC, int, const CGEN_FIELDS *);
#include "safe-ctype.h"

/* Immediate values are prefixed with '#'.  */

#define CGEN_PRINT_NORMAL(cd, info, value, attrs, pc, length) \
    do \
      { \
        if (CGEN_BOOL_ATTR ((attrs), CGEN_OPERAND_HASH_PREFIX)) \
            (*info->fprintf_func)(info->stream, "#"); \
      } \
    while (0)

/* Handle '#' prefixes as operands.  */

static void
print_hash (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED, void *dis_info,
	    long value ATTRIBUTE_UNUSED,
	    unsigned int attrs ATTRIBUTE_UNUSED,
	    bfd_vma pc ATTRIBUTE_UNUSED, int length ATTRIBUTE_UNUSED)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  (*info->fprintf_func) (info->stream, "#");
}

/* This function does the same as print_insn_normal but expects ignoring
   first 1 or first 2 operands depending on the 3rd operand.  */

static void
nds32_print_insn_cctl (CGEN_CPU_DESC cd, void *dis_info,
		       const CGEN_INSN *insn, CGEN_FIELDS *fields,
		       bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  /* cctlst: f_32t4_ext5 field.  */
  switch (fields->f_32t4_ext5)
    {
    case 3:
    case 4:
    case 5:
    case 6:
    case 19:
    case 20:
    case 21:
    case 22:
      /* Print first 2 register operands.  */
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      break;
    case 0:
    case 1:
    case 2:
    case 11:
    case 12:
    case 16:
    case 27:
    case 28:
      /* Ignore first register operand.  */
      syn += 3;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      break;
    case 8:
    case 9:
    case 10:
    case 24:
      /* Ignore first register operand.  */
      syn += 3;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      break;
    case 7:
      /* Ignore first 2 register operands.  */
      syn += 5;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      break;
    case 15:
      /* Ignore first 2 register operands.  */
      syn += 5;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      break;
    default:
      /* Should never happen.  */
      break;
    }
}

static void
nds32_print_insn_tlbop (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
			CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction neumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  switch (fields->f_32t4_ext5)
    {
    case 5:
      /* Print first 2 register operands.  */
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      break;
    case 0:
    case 1:
    case 2:
    case 3:
    case 4:
    case 6:
      /* Ignore first register operand.  */
      syn += 3;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      break;
    case 7:
      /* Ignore first 2 register operands.  */
      syn += 5;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);
      break;
    default:
      /* Should never happen.  */
      break;
    }
}

static void
nds32_print_insn_shift_op (CGEN_CPU_DESC cd, void *dis_info,
			   const CGEN_INSN *insn, CGEN_FIELDS *fields,
			   bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  if (0 == strcmp (CGEN_INSN_MNEMONIC (insn), "srli") && 0 == fields->f_32_rt5
      && 0 == fields->f_32_ra5 && 0 == fields->f_32t3_uimm5)
    {
      (*info->fprintf_func) (info->stream, "%s", "nop");
    }
  else
    {
      /* Print instruction mneumonics and space followed.  */
      syn = CGEN_SYNTAX_STRING (syntax);
      (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

      /* Print first 2 register operands.  */
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);

      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);

      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

      print_normal (cd, info, fields->f_32t3_uimm5,
		    0 | (1 << CGEN_OPERAND_SIGNED)
		    | (1 << CGEN_OPERAND_HASH_PREFIX),
		    pc, length);
    }
}

static void
nds32_print_insn_srai45 (CGEN_CPU_DESC cd, void *dis_info,
			 const CGEN_INSN *insn, CGEN_FIELDS *fields,
			 bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  /* Print first 1 register operands.  */
  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_16_uimm5,
		0 | (1 << CGEN_OPERAND_SIGNED)
		| (1 << CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

static void
nds32_print_insn_srli45 (CGEN_CPU_DESC cd, void *dis_info,
			 const CGEN_INSN *insn, CGEN_FIELDS *fields,
			 bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  if (0 == fields->f_16_uimm5 && 0 == fields->f_16_rt4)
    {
      (*info->fprintf_func) (info->stream, "%s", "nop16");
    }
  else
    {
      /* Print instruction mneumonics and space followed.  */
      syn = CGEN_SYNTAX_STRING (syntax);
      (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

      /* Print first 1 register operands.  */
      syn++;
      cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			 fields, CGEN_INSN_ATTRS (insn), pc, length);

      syn++;
      (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

      print_normal (cd, info, fields->f_16_uimm5,
		    0 | (1 << CGEN_OPERAND_SIGNED)
		    | (1 << CGEN_OPERAND_HASH_PREFIX),
		    pc, length);
    }
}

static void
nds32_print_insn_slli333 (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
			  CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  /* Print first 2 register operands.  */
  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_16_uimm3,
		0 | (1 << CGEN_OPERAND_SIGNED)
		| (1 << CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

static void
nds32_print_insn_slti45 (CGEN_CPU_DESC cd, void *dis_info,
			 const CGEN_INSN *insn, CGEN_FIELDS *fields,
			 bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  /* Print first 1 register operands.  */
  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_16_uimm5,
		0 | (1 << CGEN_OPERAND_SIGNED)
		| (1 << CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

static void
nds32_print_insn_sltsi45 (CGEN_CPU_DESC cd, void *dis_info,
			  const CGEN_INSN *insn, CGEN_FIELDS *fields,
			  bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  /* Print first 1 register operands.  */
  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_16_uimm5,
		0 | (1 << CGEN_OPERAND_SIGNED)
		| (1 << CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

static void
nds32_print_insn_arith_op45 (CGEN_CPU_DESC cd, void *dis_info,
			     const CGEN_INSN *insn, CGEN_FIELDS *fields,
			     bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  /* Print first 1 register operands.  */
  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_16_uimm5,
		0 | (1 << CGEN_OPERAND_SIGNED)
		| (1 << CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

static void
nds32_print_insn_arith_op333 (CGEN_CPU_DESC cd, void *dis_info,
			      const CGEN_INSN *insn, CGEN_FIELDS *fields,
			      bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  /* Print first 2 register operands.  */
  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_16_uimm3,
		1 << CGEN_OPERAND_SIGNED | 1 << CGEN_OPERAND_HASH_PREFIX, pc,
		length);
}

static void
nds32_print_insn_swid15 (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
			 CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_32t3_swid15,
		0 | (1 << CGEN_OPERAND_SIGNED)	
		| (1 << CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

static void
nds32_print_insn_swid15_reg (CGEN_CPU_DESC cd, void *dis_info,
			     const CGEN_INSN *insn, CGEN_FIELDS *fields,
			     bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  /* Print first 1 register operands.  */
  syn++;
  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
		     fields, CGEN_INSN_ATTRS (insn), pc, length);

  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_32t3_swid15,
		0 | (1 << CGEN_OPERAND_SIGNED) | (1 <<
						  CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

ATTRIBUTE_UNUSED static void
nds32_print_insn_swid5 (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
			CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_16_swid5,
		0 | (1 << CGEN_OPERAND_SIGNED)
		| (1 << CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

static void
print_unsigned_immediate (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
			  void *dis_info, long value,
			  unsigned int attrs ATTRIBUTE_UNUSED,
			  bfd_vma pc ATTRIBUTE_UNUSED,
			  int length ATTRIBUTE_UNUSED)
{
  disassemble_info *info = dis_info;
  (*info->fprintf_func) (info->stream, "#%d", (int) value);
}

ATTRIBUTE_UNUSED static void
nds32_print_insn_swid9 (CGEN_CPU_DESC cd, void *dis_info,
			const CGEN_INSN *insn, CGEN_FIELDS *fields,
			bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  /* Print instruction mneumonics and space followed.  */
  syn = CGEN_SYNTAX_STRING (syntax);
  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
  syn++;
  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));

  print_normal (cd, info, fields->f_16_swid9,
		0 | (1 << CGEN_OPERAND_SIGNED)
		| (1 << CGEN_OPERAND_HASH_PREFIX),
		pc, length);
}

static void
nds32_print_insn_load_store_imm (CGEN_CPU_DESC cd, void *dis_info,
				 const CGEN_INSN *insn, CGEN_FIELDS *fields,
				 bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  for (syn = CGEN_SYNTAX_STRING (syntax); *syn; ++syn)
    {
      if (CGEN_SYNTAX_MNEMONIC_P (*syn))
	{
	  (*info->fprintf_func) (info->stream, "%s",
				 CGEN_INSN_MNEMONIC (insn));
	  continue;
	}
      if (CGEN_SYNTAX_CHAR_P (*syn))
	{
	  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
	  continue;
	}

      /* We have an operand.  */
      if (NDS32_OPERAND_SLO15W == CGEN_SYNTAX_FIELD (*syn))
	{
	  /* Immediate field.  */
#ifdef CGEN_PRINT_NORMAL
	  CGEN_PRINT_NORMAL (cd, info, fields->f_32t2_slo15w,
			     0 | (1 << CGEN_OPERAND_SIGNED)
			     | (1 << CGEN_OPERAND_HASH_PREFIX),
			     pc, length);
#endif
	  if (fields->f_32t2_slo15w & 0x80000000)
	    {
	      long temp;

	      (*info->fprintf_func) (info->stream, "%s", "-0x");
	      temp = fields->f_32t2_slo15w;
	      temp = ~temp;
	      temp++;
	      (*info->fprintf_func) (info->stream, "%lx", temp);
	    }
	  else
	    {
	      (*info->fprintf_func) (info->stream, "%s", "0x");
	      (*info->fprintf_func) (info->stream, "%lx",
				     fields->f_32t2_slo15w);
	    }
	}
      else if (NDS32_OPERAND_SLO15H == CGEN_SYNTAX_FIELD (*syn))
	{
	  /* Immediate field.  */
#ifdef CGEN_PRINT_NORMAL
	  CGEN_PRINT_NORMAL (cd, info, fields->f_32t2_slo15h,
			     0 | (1 << CGEN_OPERAND_SIGNED)
			     | (1 << CGEN_OPERAND_HASH_PREFIX),
			     pc, length);
#endif
	  if (fields->f_32t2_slo15h & 0x80000000)
	    {
	      long temp;

	      (*info->fprintf_func) (info->stream, "%s", "-0x");
	      temp = fields->f_32t2_slo15h;
	      temp = ~temp;
	      temp++;
	      (*info->fprintf_func) (info->stream, "%lx", temp);
	    }
	  else
	    {
	      (*info->fprintf_func) (info->stream, "%s", "0x");
	      (*info->fprintf_func) (info->stream, "%lx",
				     fields->f_32t2_slo15h);
	    }
	}
      else if (NDS32_OPERAND_SLO15B == CGEN_SYNTAX_FIELD (*syn))
	{
	  /* Immediate field.  */
#ifdef CGEN_PRINT_NORMAL
	  CGEN_PRINT_NORMAL (cd, info, fields->f_32t2_slo15b,
			     0 | (1 << CGEN_OPERAND_SIGNED)
			     | (1 << CGEN_OPERAND_HASH_PREFIX),
			     pc, length);
#endif
	  if (fields->f_32t2_slo15b & 0x80000000)
	    {
	      long temp;

	      (*info->fprintf_func) (info->stream, "%s", "-0x");
	      temp = fields->f_32t2_slo15b;
	      temp = ~temp;
	      temp++;
	      (*info->fprintf_func) (info->stream, "%lx", temp);
	    }
	  else
	    {
	      (*info->fprintf_func) (info->stream, "%s", "0x");
	      (*info->fprintf_func) (info->stream, "%lx",
				     fields->f_32t2_slo15b);
	    }
	}
      else
	{
	  /* Register field.  */
	  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			     fields, CGEN_INSN_ATTRS (insn), pc,
			     length);
	}
    }
}

static void
print_insn_lsmw (CGEN_CPU_DESC cd, void *dis_info,
		 const CGEN_INSN *insn, CGEN_FIELDS *fields, bfd_vma pc,
		 int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;
  char forerunner = 0;

  CGEN_INIT_PRINT (cd);

  for (syn = CGEN_SYNTAX_STRING (syntax); *syn; ++syn)
    {
      if (CGEN_SYNTAX_MNEMONIC_P (*syn))
	(*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
      else if (CGEN_SYNTAX_CHAR_P (*syn))
	(*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      else if (CGEN_SYNTAX_FIELD (*syn) == NDS32_OPERAND_MASK4)
	{
	  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			     fields, CGEN_INSN_ATTRS (insn), pc,
			     length);
	}
      else
	{
	  cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
			     fields, CGEN_INSN_ATTRS (insn), pc,
			     length);
	}
    }

  (*info->fprintf_func) (info->stream, "    ! {");

  if (fields->f_32_rt5 == fields->f_32_rb5)
    {
      if (fields->f_32_rt5 != 31)
	{
	  cd->print_operand (cd, NDS32_OPERAND_RT5, info, fields,
			     CGEN_INSN_ATTRS (insn), pc, length);
	  forerunner = 1;
	}
    }
  else
    {
      cd->print_operand (cd, NDS32_OPERAND_RT5, info, fields,
			 CGEN_INSN_ATTRS (insn), pc, length);
      (*info->fprintf_func) (info->stream, "~");
      cd->print_operand (cd, NDS32_OPERAND_RB5, info, fields,
			 CGEN_INSN_ATTRS (insn), pc, length);
      forerunner = 1;
    }
  if (0x8 & fields->f_32t5_mask4)
    {
      if (forerunner)
	(*info->fprintf_func) (info->stream, ", ");
      (*info->fprintf_func) (info->stream, "$fp");
      forerunner = 1;
    }
  if (0x4 & fields->f_32t5_mask4)
    {
      if (forerunner)
	(*info->fprintf_func) (info->stream, ", ");
      (*info->fprintf_func) (info->stream, "$gp");
      forerunner = 1;
    }
  if (0x2 & fields->f_32t5_mask4)
    {
      if (forerunner)
	(*info->fprintf_func) (info->stream, ", ");
      (*info->fprintf_func) (info->stream, "$lp");
      forerunner = 1;
    }
  if (0x1 & fields->f_32t5_mask4)
    {
      if (forerunner)
	(*info->fprintf_func) (info->stream, ", ");
      (*info->fprintf_func) (info->stream, "$sp");
      forerunner = 1;
    }
  (*info->fprintf_func) (info->stream, "}");
}

static void
print_insn_push_pop (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
		     CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  for (syn = CGEN_SYNTAX_STRING (syntax); *syn; ++syn)
    {
      if (CGEN_SYNTAX_MNEMONIC_P (*syn))
	(*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
      else if (CGEN_SYNTAX_CHAR_P (*syn))
	(*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
      else
	cd->print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info, fields,
			   CGEN_INSN_ATTRS (insn), pc, length);
    }

  (*info->fprintf_func) (info->stream, "    ! {");
  if (fields->f_16_mask2 != 0)
    (*info->fprintf_func) (info->stream, "$r6~");
  cd->print_operand (cd, NDS32_OPERAND_REGLIST, info, fields,
		     CGEN_INSN_ATTRS (insn), pc, length);
  (*info->fprintf_func) (info->stream, ", $fp, $gp, $lp}");

}

static void
print_insn_eit (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
		CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  static asymbol *itb = NULL;
  disassemble_info *info = (disassemble_info *) dis_info;
  int idx;
  bfd_byte buffer[CGEN_MAX_INSN_SIZE];
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  print_insn_normal (cd, dis_info, insn, fields, pc, length);

  /* Lookup itb symbol. */
  if (!itb)
    {
      int i;

      for (i = 0; i < info->symtab_size; i++)
	if (bfd_asymbol_name (info->symtab[i])
	    && strcmp (bfd_asymbol_name (info->symtab[i]), "_ITB_BASE_") == 0)
	  {
	    itb = info->symtab[i];
	  }

      /* Lookup it only once, in case _ITB_BASE_ doesn't exist at all.  */
      if (itb == NULL)
	itb = (void *) -1;
    }

  if (itb == (void *) -1)
    return;

  /* Get ex9.it index value from first operand.  */
  syn = CGEN_SYNTAX_STRING (CGEN_INSN_SYNTAX (insn));
  idx = nds32_cgen_get_int_operand (cd, CGEN_SYNTAX_FIELD (syn[2]), fields);

  /* Print indentation. (We cannot get the value of SFILE.pos.) */
  if (idx > 9)
    (*info->fprintf_func) (info->stream, "          ! ");
  else
    (*info->fprintf_func) (info->stream, "           ! ");
  /* Fetch instruction.  */
  bfd_get_section_contents (itb->section->owner, itb->section, buffer,
			    idx * 4, CGEN_MAX_INSN_SIZE);
  print_insn (cd, bfd_asymbol_value (itb) + idx * 4, info,
	      buffer, CGEN_MAX_INSN_SIZE);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_cpe1 (CGEN_CPU_DESC cd,
		       void *dis_info,
		       const CGEN_INSN *insn,
		       CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_cpe2 (CGEN_CPU_DESC cd,
		       void *dis_info,
		       const CGEN_INSN *insn,
		       CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_cpe3 (CGEN_CPU_DESC cd,
		       void *dis_info,
		       const CGEN_INSN *insn,
		       CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_cpe4 (CGEN_CPU_DESC cd,
		       void *dis_info,
		       const CGEN_INSN *insn,
		       CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_mfcpw (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
			CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_mfcppw (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
			 CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_mfcpd (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
			CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_mtcpw (CGEN_CPU_DESC cd, void *dis_info, const CGEN_INSN *insn,
			CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_mtcppw (CGEN_CPU_DESC cd,
			 void *dis_info,
			 const CGEN_INSN *insn,
			 CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_mtcpd (CGEN_CPU_DESC cd,
			void *dis_info,
			const CGEN_INSN *insn,
			CGEN_FIELDS *fields, bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_cp_load_store_rr (CGEN_CPU_DESC cd,
				   void *dis_info,
				   const CGEN_INSN *insn,
				   CGEN_FIELDS *fields,
				   bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_cp_load_store_rr_bi (CGEN_CPU_DESC cd,
				      void *dis_info,
				      const CGEN_INSN *insn,
				      CGEN_FIELDS *fields,
				      bfd_vma pc, int length)
{
  nds32_print_insn_cp_load_store_rr (cd, dis_info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_cp_load_store_ri (CGEN_CPU_DESC cd, void *dis_info,
				   const CGEN_INSN *insn, CGEN_FIELDS *fields,
				   bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

/* This function does the same as print_insn_normal but print out user
   defined syntax.  */

static void
nds32_print_insn_cp_load_store_ri_bi (CGEN_CPU_DESC cd, void *dis_info,
				      const CGEN_INSN *insn,
				      CGEN_FIELDS *fields,
				      bfd_vma pc, int length)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  CGEN_INIT_PRINT (cd);

  print_insn_normal (cd, info, insn, fields, pc, length);
}

#undef  CGEN_PRINT_INSN
#define CGEN_PRINT_INSN nds32_print_insn

static int
nds32_print_insn (CGEN_CPU_DESC cd, bfd_vma pc, disassemble_info *info)
{
  bfd_byte buffer[CGEN_MAX_INSN_SIZE];
  bfd_byte *buf = buffer;
  int status, buflen;

  buflen = cd->base_insn_bitsize / 8;

  /* Read the base part of the insn.  */
  status = (*info->read_memory_func) (pc, buf, buflen, info);

  if (status != 0)
    {
      /* Out of cound?  Try half length instruction.  */
      buflen >>= 1;
      status = (*info->read_memory_func) (pc, buf, buflen, info);
      if (status != 0)
	{
	  (*info->memory_error_func) (status, pc, info);
	  return -1;
	}
    }
  else if ((buffer[0] & 0x80) == 0x80)
    buflen = 2;

  return print_insn (cd, pc, info, buf, buflen);
}

/* -- */

void nds32_cgen_print_operand
  (CGEN_CPU_DESC, int, PTR, CGEN_FIELDS *, void const *, bfd_vma, int);

/* Main entry point for printing operands.
   XINFO is a `void *' and not a `disassemble_info *' to not put a requirement
   of dis-asm.h on cgen.h.

   This function is basically just a big switch statement.  Earlier versions
   used tables to look up the function to use, but
   - if the table contains both assembler and disassembler functions then
     the disassembler contains much of the assembler and vice-versa,
   - there's a lot of inlining possibilities as things grow,
   - using a switch statement avoids the function call overhead.

   This function could be moved into `print_insn_normal', but keeping it
   separate makes clear the interface between `print_insn_normal' and each of
   the handlers.  */

void
nds32_cgen_print_operand (CGEN_CPU_DESC cd,
			   int opindex,
			   void * xinfo,
			   CGEN_FIELDS *fields,
			   void const *attrs ATTRIBUTE_UNUSED,
			   bfd_vma pc,
			   int length)
{
  disassemble_info *info = (disassemble_info *) xinfo;

  switch (opindex)
    {
    case NDS32_OPERAND_AR2IDX5_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ai_ar2idx5, fields->f_32_aridx5_a, 0);
      break;
    case NDS32_OPERAND_ARIDX4_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ai_aridx4, fields->f_32_aridx4_a, 0);
      break;
    case NDS32_OPERAND_ARIDX5_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ai_aridx5, fields->f_32_aridx5_a, 0);
      break;
    case NDS32_OPERAND_BITS :
      print_keyword (cd, info, & nds32_cgen_opval_h_xlsb, fields->f_16_uimm3, 0|(1<<CGEN_OPERAND_HASH_PREFIX));
      break;
    case NDS32_OPERAND_C1_15_A :
      print_normal (cd, info, fields->f_32_c1_15_a, 0, pc, length);
      break;
    case NDS32_OPERAND_CCTLLVL :
      print_keyword (cd, info, & nds32_cgen_opval_h_cctllvl, fields->f_32tx_1_21, 0);
      break;
    case NDS32_OPERAND_CCTLST :
      print_keyword (cd, info, & nds32_cgen_opval_h_cctlst, fields->f_32t4_ext5, 0);
      break;
    case NDS32_OPERAND_CONCAT24 :
      print_address (cd, info, fields->f_32_concat24, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_RELAX)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_COPDR :
      print_keyword (cd, info, & nds32_cgen_opval_cpr_names, fields->f_32_rt5, 0);
      break;
    case NDS32_OPERAND_COPWR :
      print_keyword (cd, info, & nds32_cgen_opval_cpr_names, fields->f_32_rt5, 0);
      break;
    case NDS32_OPERAND_CPID :
      print_normal (cd, info, fields->f_32_2_26, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_CPID2 :
      print_normal (cd, info, fields->f_32tx_2_17, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_D1_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ar_accum, fields->f_32_d1_a, 0);
      break;
    case NDS32_OPERAND_DH2_16_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ar_accum1, fields->f_32_dh2_16_a, 0);
      break;
    case NDS32_OPERAND_DH2_6_A :
      print_keyword (cd, info, & nds32_cgen_opval_accum_hl_names, fields->f_32_dh2_6_a, 0);
      break;
    case NDS32_OPERAND_DISP14 :
      print_address (cd, info, fields->f_32t2_disp14, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_RELAX)|(1<<CGEN_OPERAND_HASH_PREFIX)|(1<<CGEN_OPERAND_RELOC)|(1<<CGEN_OPERAND_PCREL_ADDR), pc, length);
      break;
    case NDS32_OPERAND_DISP16 :
      print_address (cd, info, fields->f_32t1_disp16, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_RELAX)|(1<<CGEN_OPERAND_HASH_PREFIX)|(1<<CGEN_OPERAND_RELOC)|(1<<CGEN_OPERAND_PCREL_ADDR), pc, length);
      break;
    case NDS32_OPERAND_DISP24 :
      print_address (cd, info, fields->f_32t0_disp24, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_RELAX)|(1<<CGEN_OPERAND_HASH_PREFIX)|(1<<CGEN_OPERAND_RELOC)|(1<<CGEN_OPERAND_PCREL_ADDR), pc, length);
      break;
    case NDS32_OPERAND_DISP8 :
      print_address (cd, info, fields->f_32t1_disp8, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_RELAX)|(1<<CGEN_OPERAND_RELOC)|(1<<CGEN_OPERAND_PCREL_ADDR), pc, length);
      break;
    case NDS32_OPERAND_DISP9 :
      print_address (cd, info, fields->f_32t1_disp9, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_RELAX)|(1<<CGEN_OPERAND_HASH_PREFIX)|(1<<CGEN_OPERAND_RELOC)|(1<<CGEN_OPERAND_PCREL_ADDR), pc, length);
      break;
    case NDS32_OPERAND_DPREFST :
      print_keyword (cd, info, & nds32_cgen_opval_h_dprefst, fields->f_32t2_st4, 0);
      break;
    case NDS32_OPERAND_FDRA5 :
      print_keyword (cd, info, & nds32_cgen_opval_h_fdr, fields->f_32_ra5, 0);
      break;
    case NDS32_OPERAND_FDRB5 :
      print_keyword (cd, info, & nds32_cgen_opval_h_fdr, fields->f_32_rb5, 0);
      break;
    case NDS32_OPERAND_FDRT5 :
      print_keyword (cd, info, & nds32_cgen_opval_h_fdr, fields->f_32_rt5, 0);
      break;
    case NDS32_OPERAND_FSRA5 :
      print_keyword (cd, info, & nds32_cgen_opval_fsr_names, fields->f_32_ra5, 0);
      break;
    case NDS32_OPERAND_FSRB5 :
      print_keyword (cd, info, & nds32_cgen_opval_fsr_names, fields->f_32_rb5, 0);
      break;
    case NDS32_OPERAND_FSRT5 :
      print_keyword (cd, info, & nds32_cgen_opval_fsr_names, fields->f_32_rt5, 0);
      break;
    case NDS32_OPERAND_GROUPIDX :
      print_normal (cd, info, fields->f_32_group, 0, pc, length);
      break;
    case NDS32_OPERAND_HASH :
      print_hash (cd, info, 0, 0|(1<<CGEN_OPERAND_SIGNED), pc, length);
      break;
    case NDS32_OPERAND_HSDISP8 :
      print_address (cd, info, fields->f_16_hsdisp8, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_RELAX)|(1<<CGEN_OPERAND_RELOC)|(1<<CGEN_OPERAND_PCREL_ADDR), pc, length);
      break;
    case NDS32_OPERAND_I2_1_A :
      print_normal (cd, info, fields->f_32_i2_1_a, 0, pc, length);
      break;
    case NDS32_OPERAND_IM1_4_A :
      print_normal (cd, info, fields->f_32_im1_4_a, 0, pc, length);
      break;
    case NDS32_OPERAND_IM5_I_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ar_i, fields->f_32_im5_i_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_IM5_M_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ar_m, fields->f_32_im5_m_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_IM6_I_0_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ar_i_lo, fields->f_32_im6_i_0_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_IM6_I_1_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ar_i_hi, fields->f_32_im6_i_1_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_IM6_M_0_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ar_m_lo, fields->f_32_im6_m_0_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_IM6_M_1_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_ar_m_hi, fields->f_32_im6_m_1_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_IMM16_A :
      print_normal (cd, info, fields->f_32_imm16_a, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_IMM5U :
      print_normal (cd, info, fields->f_16_uimm5, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_LSBLOC_A :
      print_normal (cd, info, fields->f_32_lsbloc_a, 0, pc, length);
      break;
    case NDS32_OPERAND_M2_3_A :
      print_normal (cd, info, fields->f_32_m2_3_a, 0, pc, length);
      break;
    case NDS32_OPERAND_M2_5_A :
      print_normal (cd, info, fields->f_32_m2_5_a, 0, pc, length);
      break;
    case NDS32_OPERAND_MASK4 :
      print_normal (cd, info, fields->f_32t5_mask4, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_MFUSRIDX :
      print_keyword (cd, info, & nds32_cgen_opval_h_mfusridx, fields->f_32_group_usr, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_MSYNCST :
      print_keyword (cd, info, & nds32_cgen_opval_h_msyncst, fields->f_32t3_ext3, 0);
      break;
    case NDS32_OPERAND_MTUSRIDX :
      print_keyword (cd, info, & nds32_cgen_opval_h_mtusridx, fields->f_32_group_usr, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10A5_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo, fields->f_32_r10a5_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10A5_A_B :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo_bottom, fields->f_32_r10a5_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10A5_A_T :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo_top, fields->f_32_r10a5_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10B5_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo, fields->f_32_r10b5_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10B5_A_B :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo_bottom, fields->f_32_r10b5_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10B5_A_T :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo_top, fields->f_32_r10b5_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10C5_0_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo_even, fields->f_32_r10c5_0_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10C5_1_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo_odd, fields->f_32_r10c5_1_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_R10C5_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_lo, fields->f_32_r10c5_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_RA3 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names_8, fields->f_16_ra3, 0);
      break;
    case NDS32_OPERAND_RA4 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names_16, fields->f_16_ra4, 0);
      break;
    case NDS32_OPERAND_RA4_19_A :
      print_normal (cd, info, fields->f_32_ra4_19_a, 0, pc, length);
      break;
    case NDS32_OPERAND_RA5 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_ra5, 0);
      break;
    case NDS32_OPERAND_RA5_A :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_ra5_a, 0);
      break;
    case NDS32_OPERAND_RA5_A_B :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_ra5_a, 0);
      break;
    case NDS32_OPERAND_RA5_A_T :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_ra5_a, 0);
      break;
    case NDS32_OPERAND_RA5E :
      print_keyword (cd, info, & nds32_cgen_opval_even_gr_names_16, fields->f_16_ra5e, 0);
      break;
    case NDS32_OPERAND_RA5H :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_16_ra5h, 0);
      break;
    case NDS32_OPERAND_RB3 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names_8, fields->f_16_rb3, 0);
      break;
    case NDS32_OPERAND_RB3_14_A :
      print_normal (cd, info, fields->f_32_rb3_14_a, 0, pc, length);
      break;
    case NDS32_OPERAND_RB5 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rb5, 0);
      break;
    case NDS32_OPERAND_RB5_A :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rb5_a, 0);
      break;
    case NDS32_OPERAND_RB5_A_B :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rb5_a, 0);
      break;
    case NDS32_OPERAND_RB5_A_T :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rb5_a, 0);
      break;
    case NDS32_OPERAND_RB5H :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_16_rb5h, 0);
      break;
    case NDS32_OPERAND_RB5P_A :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rb5p_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_RB5P_A_B :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rb5p_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_RB5P_A_T :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rb5p_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_RC1_5_A :
      print_normal (cd, info, fields->f_32_rc1_5_a, 0, pc, length);
      break;
    case NDS32_OPERAND_RC2_11_A :
      print_normal (cd, info, fields->f_32_rc2_11_a, 0, pc, length);
      break;
    case NDS32_OPERAND_RC4_A :
      print_normal (cd, info, fields->f_32_rc4_a, 0, pc, length);
      break;
    case NDS32_OPERAND_RC5_0_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_even, fields->f_32_rc5_0_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_RC5_1_A :
      print_keyword (cd, info, & nds32_cgen_opval_h_gr_odd, fields->f_32_rc5_1_a, 0|(1<<CGEN_OPERAND_VIRTUAL));
      break;
    case NDS32_OPERAND_RD1 :
      print_keyword (cd, info, & nds32_cgen_opval_accum_names, fields->f_32_rd1, 0);
      break;
    case NDS32_OPERAND_RD1HL :
      print_keyword (cd, info, & nds32_cgen_opval_accum_hl_names, fields->f_32_rd1hl, 0);
      break;
    case NDS32_OPERAND_RD5_A :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rd5_a, 0);
      break;
    case NDS32_OPERAND_REGLIST :
      print_keyword (cd, info, & nds32_cgen_opval_h_reglist, fields->f_16_mask2, 0);
      break;
    case NDS32_OPERAND_RS5 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rs5, 0);
      break;
    case NDS32_OPERAND_RT3 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names_8, fields->f_16_rt3, 0);
      break;
    case NDS32_OPERAND_RT3_7 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names_8, fields->f_16_rt3_7, 0);
      break;
    case NDS32_OPERAND_RT3E5 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names_8e5, fields->f_16_rt3, 0);
      break;
    case NDS32_OPERAND_RT4 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names_16, fields->f_16_rt4, 0);
      break;
    case NDS32_OPERAND_RT5 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rt5, 0);
      break;
    case NDS32_OPERAND_RT5E :
      print_keyword (cd, info, & nds32_cgen_opval_even_gr_names_16, fields->f_16_rt5e, 0);
      break;
    case NDS32_OPERAND_RT5H :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_16_rt5h, 0);
      break;
    case NDS32_OPERAND_RTH5 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_rt5, 0);
      break;
    case NDS32_OPERAND_RTL5 :
      print_keyword (cd, info, & nds32_cgen_opval_gr_names, fields->f_32_ra5, 0);
      break;
    case NDS32_OPERAND_SI :
      print_normal (cd, info, fields->f_32t3_sub10si, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SIMM10 :
      print_normal (cd, info, fields->f_16_simm10, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SIMM11 :
      print_normal (cd, info, fields->f_32t2_simm11, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SIMM5H :
      print_normal (cd, info, fields->f_16_simm5, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SIMM5W :
      print_normal (cd, info, fields->f_16_simm5w, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO12D :
      print_normal (cd, info, fields->f_32tx_slo12d, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO12W :
      print_normal (cd, info, fields->f_32tx_slo12w, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO15 :
      print_normal (cd, info, fields->f_32t2_slo15b, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO15B :
      print_normal (cd, info, fields->f_32t2_slo15b, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO15D :
      print_normal (cd, info, fields->f_32t2_slo15d, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO15H :
      print_normal (cd, info, fields->f_32t2_slo15h, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO15W :
      print_normal (cd, info, fields->f_32t2_slo15w, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO17W :
      print_normal (cd, info, fields->f_32_slo17w, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO18H :
      print_normal (cd, info, fields->f_32_slo18h, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO19 :
      print_normal (cd, info, fields->f_32_slo19, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SLO20 :
      print_normal (cd, info, fields->f_32t1_slo20, 0|(1<<CGEN_OPERAND_SIGNED)|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SR10 :
      print_keyword (cd, info, & nds32_cgen_opval_sr_names, fields->f_32_sr10, 0);
      break;
    case NDS32_OPERAND_STANDBYST :
      print_keyword (cd, info, & nds32_cgen_opval_h_standbyst, fields->f_32t4_ext2, 0);
      break;
    case NDS32_OPERAND_SUIMM5 :
      print_normal (cd, info, fields->f_16_suimm5, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SWID15 :
      print_normal (cd, info, fields->f_32t3_swid15, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SWID5 :
      print_unsigned_immediate (cd, info, fields->f_16_swid5, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_SWID9 :
      print_unsigned_immediate (cd, info, fields->f_16_swid9, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_TLBOPST :
      print_keyword (cd, info, & nds32_cgen_opval_h_tlbopst, fields->f_32t4_ext5, 0);
      break;
    case NDS32_OPERAND_UHI20 :
      print_normal (cd, info, fields->f_32t1_uhi20, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM12 :
      print_normal (cd, info, fields->f_32_12_12, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM19 :
      print_normal (cd, info, fields->f_32_19_7, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM3 :
      print_normal (cd, info, fields->f_16_uimm3, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM3_10 :
      print_normal (cd, info, fields->f_16_uimm3_10, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM5 :
      print_normal (cd, info, fields->f_32t3_uimm5, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM5D :
      print_normal (cd, info, fields->f_16_uimm5d, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM5H :
      print_normal (cd, info, fields->f_16_uimm5, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM6W :
      print_normal (cd, info, fields->f_16_uimm6w, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM8_S :
      print_normal (cd, info, fields->f_32_uimm8_s, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_UIMM_SR10 :
      print_normal (cd, info, fields->f_32_sr10, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO15 :
      print_normal (cd, info, fields->f_32t2_ulo15b, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO15B :
      print_normal (cd, info, fields->f_32t2_ulo15b, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO15D :
      print_normal (cd, info, fields->f_32t2_ulo15d, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO15H :
      print_normal (cd, info, fields->f_32t2_ulo15h, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO15W :
      print_normal (cd, info, fields->f_32t2_ulo15w, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO3B :
      print_normal (cd, info, fields->f_16_ulo3b, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO3H :
      print_normal (cd, info, fields->f_16_ulo3h, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO3W :
      print_normal (cd, info, fields->f_16_ulo3w, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO5 :
      print_normal (cd, info, fields->f_32t21_ulo5, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_ULO7W :
      print_normal (cd, info, fields->f_16_ulo7w, 0|(1<<CGEN_OPERAND_HASH_PREFIX), pc, length);
      break;
    case NDS32_OPERAND_USRIDX :
      print_normal (cd, info, fields->f_32_usr, 0, pc, length);
      break;

    default :
      /* xgettext:c-format */
      fprintf (stderr, _("Unrecognized field %d while printing insn.\n"),
	       opindex);
    abort ();
  }
}

cgen_print_fn * const nds32_cgen_print_handlers[] = 
{
  print_insn_normal,
  print_insn_special9,
  print_insn_special20,
  print_insn_lsmw,
  print_insn_special17,
  print_insn_special18,
  print_insn_special1,
  print_insn_special0,
  print_insn_special15,
  print_insn_special10,
  print_insn_special11,
  print_insn_special12,
  print_insn_special16,
  print_insn_special13,
  print_insn_special14,
  print_insn_push_pop,
  print_insn_special21,
  print_insn_special22,
  print_insn_special23,
  print_insn_special24,
  print_insn_special31,
  print_insn_special32,
  print_insn_special33,
  print_insn_special34,
  print_insn_special4,
  print_insn_special6,
  print_insn_special3,
  print_insn_special5,
  print_insn_special7,
  print_insn_special8,
  print_insn_eit,
};


void
nds32_cgen_init_dis (CGEN_CPU_DESC cd)
{
  nds32_cgen_init_opcode_table (cd);
  nds32_cgen_init_ibld_table (cd);
  cd->print_handlers = & nds32_cgen_print_handlers[0];
  cd->print_operand = nds32_cgen_print_operand;
}


/* Default print handler.  */

static void
print_normal (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
	      void *dis_info,
	      long value,
	      unsigned int attrs,
	      bfd_vma pc ATTRIBUTE_UNUSED,
	      int length ATTRIBUTE_UNUSED)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  /* Print the operand as directed by the attributes.  */
  if (CGEN_BOOL_ATTR (attrs, CGEN_OPERAND_SEM_ONLY))
    ; /* nothing to do */
  else if (CGEN_BOOL_ATTR (attrs, CGEN_OPERAND_SIGNED))
    (*info->fprintf_func) (info->stream, "%ld", value);
  else
    (*info->fprintf_func) (info->stream, "0x%lx", value);
}

/* Default address handler.  */

static void
print_address (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
	       void *dis_info,
	       bfd_vma value,
	       unsigned int attrs,
	       bfd_vma pc ATTRIBUTE_UNUSED,
	       int length ATTRIBUTE_UNUSED)
{
  disassemble_info *info = (disassemble_info *) dis_info;

  /* Print the operand as directed by the attributes.  */
  if (CGEN_BOOL_ATTR (attrs, CGEN_OPERAND_SEM_ONLY))
    ; /* Nothing to do.  */
  else if (CGEN_BOOL_ATTR (attrs, CGEN_OPERAND_PCREL_ADDR))
    (*info->print_address_func) (value, info);
  else if (CGEN_BOOL_ATTR (attrs, CGEN_OPERAND_ABS_ADDR))
    (*info->print_address_func) (value, info);
  else if (CGEN_BOOL_ATTR (attrs, CGEN_OPERAND_SIGNED))
    (*info->fprintf_func) (info->stream, "%ld", (long) value);
  else
    (*info->fprintf_func) (info->stream, "0x%lx", (long) value);
}

/* Keyword print handler.  */

static void
print_keyword (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
	       void *dis_info,
	       CGEN_KEYWORD *keyword_table,
	       long value,
	       unsigned int attrs ATTRIBUTE_UNUSED)
{
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_KEYWORD_ENTRY *ke;

  ke = cgen_keyword_lookup_value (keyword_table, value);
  if (ke != NULL)
    (*info->fprintf_func) (info->stream, "%s", ke->name);
  else
    (*info->fprintf_func) (info->stream, "???");
}

/* Default insn printer.

   DIS_INFO is defined as `void *' so the disassembler needn't know anything
   about disassemble_info.  */

static void
print_insn_normal (CGEN_CPU_DESC cd,
		   void *dis_info,
		   const CGEN_INSN *insn,
		   CGEN_FIELDS *fields,
		   bfd_vma pc,
		   int length)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  disassemble_info *info = (disassemble_info *) dis_info;
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_INIT_PRINT (cd);

  for (syn = CGEN_SYNTAX_STRING (syntax); *syn; ++syn)
    {
      if (CGEN_SYNTAX_MNEMONIC_P (*syn))
	{
	  (*info->fprintf_func) (info->stream, "%s", CGEN_INSN_MNEMONIC (insn));
	  continue;
	}
      if (CGEN_SYNTAX_CHAR_P (*syn))
	{
	  (*info->fprintf_func) (info->stream, "%c", CGEN_SYNTAX_CHAR (*syn));
	  continue;
	}

      /* We have an operand.  */
      nds32_cgen_print_operand (cd, CGEN_SYNTAX_FIELD (*syn), info,
				 fields, CGEN_INSN_ATTRS (insn), pc, length);
    }
}

/* Subroutine of print_insn. Reads an insn into the given buffers and updates
   the extract info.
   Returns 0 if all is well, non-zero otherwise.  */

static int
read_insn (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
	   bfd_vma pc,
	   disassemble_info *info,
	   bfd_byte *buf,
	   int buflen,
	   CGEN_EXTRACT_INFO *ex_info,
	   unsigned long *insn_value)
{
  int status = (*info->read_memory_func) (pc, buf, buflen, info);

  if (status != 0)
    {
      (*info->memory_error_func) (status, pc, info);
      return -1;
    }

  ex_info->dis_info = info;
  ex_info->valid = (1 << buflen) - 1;
  ex_info->insn_bytes = buf;

  *insn_value = bfd_get_bits (buf, buflen * 8, info->endian == BFD_ENDIAN_BIG);
  return 0;
}

/* Utility to print an insn.
   BUF is the base part of the insn, target byte order, BUFLEN bytes long.
   The result is the size of the insn in bytes or zero for an unknown insn
   or -1 if an error occurs fetching data (memory_error_func will have
   been called).  */

static int
print_insn (CGEN_CPU_DESC cd,
	    bfd_vma pc,
	    disassemble_info *info,
	    bfd_byte *buf,
	    unsigned int buflen)
{
  CGEN_INSN_INT insn_value;
  const CGEN_INSN_LIST *insn_list;
  CGEN_EXTRACT_INFO ex_info;
  int basesize;

  /* Extract base part of instruction, just in case CGEN_DIS_* uses it. */
  basesize = cd->base_insn_bitsize < buflen * 8 ?
                                     cd->base_insn_bitsize : buflen * 8;
  insn_value = cgen_get_insn_value (cd, buf, basesize);


  /* Fill in ex_info fields like read_insn would.  Don't actually call
     read_insn, since the incoming buffer is already read (and possibly
     modified a la m32r).  */
  ex_info.valid = (1 << buflen) - 1;
  ex_info.dis_info = info;
  ex_info.insn_bytes = buf;

  /* The instructions are stored in hash lists.
     Pick the first one and keep trying until we find the right one.  */

  insn_list = CGEN_DIS_LOOKUP_INSN (cd, (char *) buf, insn_value);
  while (insn_list != NULL)
    {
      const CGEN_INSN *insn = insn_list->insn;
      CGEN_FIELDS fields;
      int length;
      unsigned long insn_value_cropped;

#ifdef CGEN_VALIDATE_INSN_SUPPORTED 
      /* Not needed as insn shouldn't be in hash lists if not supported.  */
      /* Supported by this cpu?  */
      if (! nds32_cgen_insn_supported (cd, insn))
        {
          insn_list = CGEN_DIS_NEXT_INSN (insn_list);
	  continue;
        }
#endif

      /* Basic bit mask must be correct.  */
      /* ??? May wish to allow target to defer this check until the extract
	 handler.  */

      /* Base size may exceed this instruction's size.  Extract the
         relevant part from the buffer. */
      if ((unsigned) (CGEN_INSN_BITSIZE (insn) / 8) < buflen &&
	  (unsigned) (CGEN_INSN_BITSIZE (insn) / 8) <= sizeof (unsigned long))
	insn_value_cropped = bfd_get_bits (buf, CGEN_INSN_BITSIZE (insn), 
					   info->endian == BFD_ENDIAN_BIG);
      else
	insn_value_cropped = insn_value;

      if ((insn_value_cropped & CGEN_INSN_BASE_MASK (insn))
	  == CGEN_INSN_BASE_VALUE (insn))
	{
	  /* Printing is handled in two passes.  The first pass parses the
	     machine insn and extracts the fields.  The second pass prints
	     them.  */

	  /* Make sure the entire insn is loaded into insn_value, if it
	     can fit.  */
	  if (((unsigned) CGEN_INSN_BITSIZE (insn) > cd->base_insn_bitsize) &&
	      (unsigned) (CGEN_INSN_BITSIZE (insn) / 8) <= sizeof (unsigned long))
	    {
	      unsigned long full_insn_value;
	      int rc = read_insn (cd, pc, info, buf,
				  CGEN_INSN_BITSIZE (insn) / 8,
				  & ex_info, & full_insn_value);
	      if (rc != 0)
		return rc;
	      length = CGEN_EXTRACT_FN (cd, insn)
		(cd, insn, &ex_info, full_insn_value, &fields, pc);
	    }
	  else
	    length = CGEN_EXTRACT_FN (cd, insn)
	      (cd, insn, &ex_info, insn_value_cropped, &fields, pc);

	  /* Length < 0 -> error.  */
	  if (length < 0)
	    return length;
	  if (length > 0)
	    {
	      CGEN_PRINT_FN (cd, insn) (cd, info, insn, &fields, pc, length);
	      /* Length is in bits, result is in bytes.  */
	      return length / 8;
	    }
	}

      insn_list = CGEN_DIS_NEXT_INSN (insn_list);
    }

  return 0;
}

/* Default value for CGEN_PRINT_INSN.
   The result is the size of the insn in bytes or zero for an unknown insn
   or -1 if an error occured fetching bytes.  */

#ifndef CGEN_PRINT_INSN
#define CGEN_PRINT_INSN default_print_insn
#endif

static int
default_print_insn (CGEN_CPU_DESC cd, bfd_vma pc, disassemble_info *info)
{
  bfd_byte buf[CGEN_MAX_INSN_SIZE];
  int buflen;
  int status;

  /* Attempt to read the base part of the insn.  */
  buflen = cd->base_insn_bitsize / 8;
  status = (*info->read_memory_func) (pc, buf, buflen, info);

  /* Try again with the minimum part, if min < base.  */
  if (status != 0 && (cd->min_insn_bitsize < cd->base_insn_bitsize))
    {
      buflen = cd->min_insn_bitsize / 8;
      status = (*info->read_memory_func) (pc, buf, buflen, info);
    }

  if (status != 0)
    {
      (*info->memory_error_func) (status, pc, info);
      return -1;
    }

  return print_insn (cd, pc, info, buf, buflen);
}

/* Main entry point.
   Print one instruction from PC on INFO->STREAM.
   Return the size of the instruction (in bytes).  */

typedef struct cpu_desc_list
{
  struct cpu_desc_list *next;
  CGEN_BITSET *isa;
  int mach;
  int endian;
  CGEN_CPU_DESC cd;
} cpu_desc_list;

int
print_insn_nds32 (bfd_vma pc, disassemble_info *info)
{
  static cpu_desc_list *cd_list = 0;
  cpu_desc_list *cl = 0;
  static CGEN_CPU_DESC cd = 0;
  static CGEN_BITSET *prev_isa;
  static int prev_mach;
  static int prev_endian;
  int length;
  CGEN_BITSET *isa;
  int mach;
  int endian = (info->endian == BFD_ENDIAN_BIG
		? CGEN_ENDIAN_BIG
		: CGEN_ENDIAN_LITTLE);
  enum bfd_architecture arch;

  /* ??? gdb will set mach but leave the architecture as "unknown" */
#ifndef CGEN_BFD_ARCH
#define CGEN_BFD_ARCH bfd_arch_nds32
#endif
  arch = info->arch;
  if (arch == bfd_arch_unknown)
    arch = CGEN_BFD_ARCH;
   
  /* There's no standard way to compute the machine or isa number
     so we leave it to the target.  */
#ifdef CGEN_COMPUTE_MACH
  mach = CGEN_COMPUTE_MACH (info);
#else
  mach = info->mach;
#endif

#ifdef CGEN_COMPUTE_ISA
  {
    static CGEN_BITSET *permanent_isa;

    if (!permanent_isa)
      permanent_isa = cgen_bitset_create (MAX_ISAS);
    isa = permanent_isa;
    cgen_bitset_clear (isa);
    cgen_bitset_add (isa, CGEN_COMPUTE_ISA (info));
  }
#else
  isa = info->insn_sets;
#endif

  /* If we've switched cpu's, try to find a handle we've used before */
  if (cd
      && (cgen_bitset_compare (isa, prev_isa) != 0
	  || mach != prev_mach
	  || endian != prev_endian))
    {
      cd = 0;
      for (cl = cd_list; cl; cl = cl->next)
	{
	  if (cgen_bitset_compare (cl->isa, isa) == 0 &&
	      cl->mach == mach &&
	      cl->endian == endian)
	    {
	      cd = cl->cd;
 	      prev_isa = cd->isas;
	      break;
	    }
	}
    } 

  /* If we haven't initialized yet, initialize the opcode table.  */
  if (! cd)
    {
      const bfd_arch_info_type *arch_type = bfd_lookup_arch (arch, mach);
      const char *mach_name;

      if (!arch_type)
	abort ();
      mach_name = arch_type->printable_name;

      prev_isa = cgen_bitset_copy (isa);
      prev_mach = mach;
      prev_endian = endian;
      cd = nds32_cgen_cpu_open (CGEN_CPU_OPEN_ISAS, prev_isa,
				 CGEN_CPU_OPEN_BFDMACH, mach_name,
				 CGEN_CPU_OPEN_ENDIAN, prev_endian,
				 CGEN_CPU_OPEN_END);
      if (!cd)
	abort ();

      /* Save this away for future reference.  */
      cl = xmalloc (sizeof (struct cpu_desc_list));
      cl->cd = cd;
      cl->isa = prev_isa;
      cl->mach = mach;
      cl->endian = endian;
      cl->next = cd_list;
      cd_list = cl;

      nds32_cgen_init_dis (cd);
    }

  /* We try to have as much common code as possible.
     But at this point some targets need to take over.  */
  /* ??? Some targets may need a hook elsewhere.  Try to avoid this,
     but if not possible try to move this hook elsewhere rather than
     have two hooks.  */
  length = CGEN_PRINT_INSN (cd, pc, info);
  if (length > 0)
    return length;
  if (length < 0)
    return -1;

  (*info->fprintf_func) (info->stream, UNKNOWN_INSN_MSG);
  return cd->default_insn_bitsize / 8;
}
