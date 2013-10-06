/* Instruction building/extraction support for nds32. -*- C -*-

   THIS FILE IS MACHINE GENERATED WITH CGEN: Cpu tools GENerator.
   - the resultant file is machine generated, cgen-ibld.in isn't

   Copyright 1996, 1997, 1998, 1999, 2000, 2001, 2005, 2006, 2007,
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
#include "nds32-desc.h"
#include "nds32-opc.h"
#include "cgen/basic-modes.h"
#include "opintl.h"
#include "safe-ctype.h"

#undef  min
#define min(a,b) ((a) < (b) ? (a) : (b))
#undef  max
#define max(a,b) ((a) > (b) ? (a) : (b))

/* Used by the ifield rtx function.  */
#define FLD(f) (fields->f)

static const char * insert_normal
  (CGEN_CPU_DESC, long, unsigned int, unsigned int, unsigned int,
   unsigned int, unsigned int, unsigned int, CGEN_INSN_BYTES_PTR);
static const char * insert_insn_normal
  (CGEN_CPU_DESC, const CGEN_INSN *,
   CGEN_FIELDS *, CGEN_INSN_BYTES_PTR, bfd_vma);
static int extract_normal
  (CGEN_CPU_DESC, CGEN_EXTRACT_INFO *, CGEN_INSN_INT,
   unsigned int, unsigned int, unsigned int, unsigned int,
   unsigned int, unsigned int, bfd_vma, long *);
static int extract_insn_normal
  (CGEN_CPU_DESC, const CGEN_INSN *, CGEN_EXTRACT_INFO *,
   CGEN_INSN_INT, CGEN_FIELDS *, bfd_vma);
#if CGEN_INT_INSN_P
static void put_insn_int_value
  (CGEN_CPU_DESC, CGEN_INSN_BYTES_PTR, int, int, CGEN_INSN_INT);
#endif
#if ! CGEN_INT_INSN_P
static CGEN_INLINE void insert_1
  (CGEN_CPU_DESC, unsigned long, int, int, int, unsigned char *);
static CGEN_INLINE int fill_cache
  (CGEN_CPU_DESC, CGEN_EXTRACT_INFO *,  int, int, bfd_vma);
static CGEN_INLINE long extract_1
  (CGEN_CPU_DESC, CGEN_EXTRACT_INFO *, int, int, int, unsigned char *, bfd_vma);
#endif

/* Operand insertion.  */

#if ! CGEN_INT_INSN_P

/* Subroutine of insert_normal.  */

static CGEN_INLINE void
insert_1 (CGEN_CPU_DESC cd,
	  unsigned long value,
	  int start,
	  int length,
	  int word_length,
	  unsigned char *bufp)
{
  unsigned long x,mask;
  int shift;

  x = cgen_get_insn_value (cd, bufp, word_length);

  /* Written this way to avoid undefined behaviour.  */
  mask = (((1L << (length - 1)) - 1) << 1) | 1;
  if (CGEN_INSN_LSB0_P)
    shift = (start + 1) - length;
  else
    shift = (word_length - (start + length));
  x = (x & ~(mask << shift)) | ((value & mask) << shift);

  cgen_put_insn_value (cd, bufp, word_length, (bfd_vma) x);
}

#endif /* ! CGEN_INT_INSN_P */

/* Default insertion routine.

   ATTRS is a mask of the boolean attributes.
   WORD_OFFSET is the offset in bits from the start of the insn of the value.
   WORD_LENGTH is the length of the word in bits in which the value resides.
   START is the starting bit number in the word, architecture origin.
   LENGTH is the length of VALUE in bits.
   TOTAL_LENGTH is the total length of the insn in bits.

   The result is an error message or NULL if success.  */

/* ??? This duplicates functionality with bfd's howto table and
   bfd_install_relocation.  */
/* ??? This doesn't handle bfd_vma's.  Create another function when
   necessary.  */

static const char *
insert_normal (CGEN_CPU_DESC cd,
	       long value,
	       unsigned int attrs,
	       unsigned int word_offset,
	       unsigned int start,
	       unsigned int length,
	       unsigned int word_length,
	       unsigned int total_length,
	       CGEN_INSN_BYTES_PTR buffer)
{
  static char errbuf[100];
  /* Written this way to avoid undefined behaviour.  */
  unsigned long mask = (((1L << (length - 1)) - 1) << 1) | 1;

  /* If LENGTH is zero, this operand doesn't contribute to the value.  */
  if (length == 0)
    return NULL;

  if (word_length > 8 * sizeof (CGEN_INSN_INT))
    abort ();

  /* For architectures with insns smaller than the base-insn-bitsize,
     word_length may be too big.  */
  if (cd->min_insn_bitsize < cd->base_insn_bitsize)
    {
      if (word_offset == 0
	  && word_length > total_length)
	word_length = total_length;
    }

  /* Ensure VALUE will fit.  */
  if (CGEN_BOOL_ATTR (attrs, CGEN_IFLD_SIGN_OPT))
    {
      long minval = - (1L << (length - 1));
      unsigned long maxval = mask;
      
      if ((value > 0 && (unsigned long) value > maxval)
	  || value < minval)
	{
	  /* xgettext:c-format */
	  sprintf (errbuf,
		   _("operand out of range (%ld not between %ld and %lu)"),
		   value, minval, maxval);
	  return errbuf;
	}
    }
  else if (! CGEN_BOOL_ATTR (attrs, CGEN_IFLD_SIGNED))
    {
      unsigned long maxval = mask;
      unsigned long val = (unsigned long) value;

      /* For hosts with a word size > 32 check to see if value has been sign
	 extended beyond 32 bits.  If so then ignore these higher sign bits
	 as the user is attempting to store a 32-bit signed value into an
	 unsigned 32-bit field which is allowed.  */
      if (sizeof (unsigned long) > 4 && ((value >> 32) == -1))
	val &= 0xFFFFFFFF;

      if (val > maxval)
	{
	  /* xgettext:c-format */
	  sprintf (errbuf,
		   _("operand out of range (0x%lx not between 0 and 0x%lx)"),
		   val, maxval);
	  return errbuf;
	}
    }
  else
    {
      if (! cgen_signed_overflow_ok_p (cd))
	{
	  long minval = - (1L << (length - 1));
	  long maxval =   (1L << (length - 1)) - 1;
	  
	  if (value < minval || value > maxval)
	    {
	      sprintf
		/* xgettext:c-format */
		(errbuf, _("operand out of range (%ld not between %ld and %ld)"),
		 value, minval, maxval);
	      return errbuf;
	    }
	}
    }

#if CGEN_INT_INSN_P

  {
    int shift;

    if (CGEN_INSN_LSB0_P)
      shift = (word_offset + start + 1) - length;
    else
      shift = total_length - (word_offset + start + length);
    *buffer = (*buffer & ~(mask << shift)) | ((value & mask) << shift);
  }

#else /* ! CGEN_INT_INSN_P */

  {
    unsigned char *bufp = (unsigned char *) buffer + word_offset / 8;

    insert_1 (cd, value, start, length, word_length, bufp);
  }

#endif /* ! CGEN_INT_INSN_P */

  return NULL;
}

/* Default insn builder (insert handler).
   The instruction is recorded in CGEN_INT_INSN_P byte order (meaning
   that if CGEN_INSN_BYTES_PTR is an int * and thus, the value is
   recorded in host byte order, otherwise BUFFER is an array of bytes
   and the value is recorded in target byte order).
   The result is an error message or NULL if success.  */

static const char *
insert_insn_normal (CGEN_CPU_DESC cd,
		    const CGEN_INSN * insn,
		    CGEN_FIELDS * fields,
		    CGEN_INSN_BYTES_PTR buffer,
		    bfd_vma pc)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  unsigned long value;
  const CGEN_SYNTAX_CHAR_TYPE * syn;

  CGEN_INIT_INSERT (cd);
  value = CGEN_INSN_BASE_VALUE (insn);

  /* If we're recording insns as numbers (rather than a string of bytes),
     target byte order handling is deferred until later.  */

#if CGEN_INT_INSN_P

  put_insn_int_value (cd, buffer, cd->base_insn_bitsize,
		      CGEN_FIELDS_BITSIZE (fields), value);

#else

  cgen_put_insn_value (cd, buffer, min ((unsigned) cd->base_insn_bitsize,
					(unsigned) CGEN_FIELDS_BITSIZE (fields)),
		       value);

#endif /* ! CGEN_INT_INSN_P */

  /* ??? It would be better to scan the format's fields.
     Still need to be able to insert a value based on the operand though;
     e.g. storing a branch displacement that got resolved later.
     Needs more thought first.  */

  for (syn = CGEN_SYNTAX_STRING (syntax); * syn; ++ syn)
    {
      const char *errmsg;

      if (CGEN_SYNTAX_CHAR_P (* syn))
	continue;

      errmsg = (* cd->insert_operand) (cd, CGEN_SYNTAX_FIELD (*syn),
				       fields, buffer, pc);
      if (errmsg)
	return errmsg;
    }

  return NULL;
}

#if CGEN_INT_INSN_P
/* Cover function to store an insn value into an integral insn.  Must go here
   because it needs <prefix>-desc.h for CGEN_INT_INSN_P.  */

static void
put_insn_int_value (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
		    CGEN_INSN_BYTES_PTR buf,
		    int length,
		    int insn_length,
		    CGEN_INSN_INT value)
{
  /* For architectures with insns smaller than the base-insn-bitsize,
     length may be too big.  */
  if (length > insn_length)
    *buf = value;
  else
    {
      int shift = insn_length - length;
      /* Written this way to avoid undefined behaviour.  */
      CGEN_INSN_INT mask = (((1L << (length - 1)) - 1) << 1) | 1;

      *buf = (*buf & ~(mask << shift)) | ((value & mask) << shift);
    }
}
#endif

/* Operand extraction.  */

#if ! CGEN_INT_INSN_P

/* Subroutine of extract_normal.
   Ensure sufficient bytes are cached in EX_INFO.
   OFFSET is the offset in bytes from the start of the insn of the value.
   BYTES is the length of the needed value.
   Returns 1 for success, 0 for failure.  */

static CGEN_INLINE int
fill_cache (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
	    CGEN_EXTRACT_INFO *ex_info,
	    int offset,
	    int bytes,
	    bfd_vma pc)
{
  /* It's doubtful that the middle part has already been fetched so
     we don't optimize that case.  kiss.  */
  unsigned int mask;
  disassemble_info *info = (disassemble_info *) ex_info->dis_info;

  /* First do a quick check.  */
  mask = (1 << bytes) - 1;
  if (((ex_info->valid >> offset) & mask) == mask)
    return 1;

  /* Search for the first byte we need to read.  */
  for (mask = 1 << offset; bytes > 0; --bytes, ++offset, mask <<= 1)
    if (! (mask & ex_info->valid))
      break;

  if (bytes)
    {
      int status;

      pc += offset;
      status = (*info->read_memory_func)
	(pc, ex_info->insn_bytes + offset, bytes, info);

      if (status != 0)
	{
	  (*info->memory_error_func) (status, pc, info);
	  return 0;
	}

      ex_info->valid |= ((1 << bytes) - 1) << offset;
    }

  return 1;
}

/* Subroutine of extract_normal.  */

static CGEN_INLINE long
extract_1 (CGEN_CPU_DESC cd,
	   CGEN_EXTRACT_INFO *ex_info ATTRIBUTE_UNUSED,
	   int start,
	   int length,
	   int word_length,
	   unsigned char *bufp,
	   bfd_vma pc ATTRIBUTE_UNUSED)
{
  unsigned long x;
  int shift;

  x = cgen_get_insn_value (cd, bufp, word_length);

  if (CGEN_INSN_LSB0_P)
    shift = (start + 1) - length;
  else
    shift = (word_length - (start + length));
  return x >> shift;
}

#endif /* ! CGEN_INT_INSN_P */

/* Default extraction routine.

   INSN_VALUE is the first base_insn_bitsize bits of the insn in host order,
   or sometimes less for cases like the m32r where the base insn size is 32
   but some insns are 16 bits.
   ATTRS is a mask of the boolean attributes.  We only need `SIGNED',
   but for generality we take a bitmask of all of them.
   WORD_OFFSET is the offset in bits from the start of the insn of the value.
   WORD_LENGTH is the length of the word in bits in which the value resides.
   START is the starting bit number in the word, architecture origin.
   LENGTH is the length of VALUE in bits.
   TOTAL_LENGTH is the total length of the insn in bits.

   Returns 1 for success, 0 for failure.  */

/* ??? The return code isn't properly used.  wip.  */

/* ??? This doesn't handle bfd_vma's.  Create another function when
   necessary.  */

static int
extract_normal (CGEN_CPU_DESC cd,
#if ! CGEN_INT_INSN_P
		CGEN_EXTRACT_INFO *ex_info,
#else
		CGEN_EXTRACT_INFO *ex_info ATTRIBUTE_UNUSED,
#endif
		CGEN_INSN_INT insn_value,
		unsigned int attrs,
		unsigned int word_offset,
		unsigned int start,
		unsigned int length,
		unsigned int word_length,
		unsigned int total_length,
#if ! CGEN_INT_INSN_P
		bfd_vma pc,
#else
		bfd_vma pc ATTRIBUTE_UNUSED,
#endif
		long *valuep)
{
  long value, mask;

  /* If LENGTH is zero, this operand doesn't contribute to the value
     so give it a standard value of zero.  */
  if (length == 0)
    {
      *valuep = 0;
      return 1;
    }

  if (word_length > 8 * sizeof (CGEN_INSN_INT))
    abort ();

  /* For architectures with insns smaller than the insn-base-bitsize,
     word_length may be too big.  */
  if (cd->min_insn_bitsize < cd->base_insn_bitsize)
    {
      if (word_offset + word_length > total_length)
	word_length = total_length - word_offset;
    }

  /* Does the value reside in INSN_VALUE, and at the right alignment?  */

  if (CGEN_INT_INSN_P || (word_offset == 0 && word_length == total_length))
    {
      if (CGEN_INSN_LSB0_P)
	value = insn_value >> ((word_offset + start + 1) - length);
      else
	value = insn_value >> (total_length - ( word_offset + start + length));
    }

#if ! CGEN_INT_INSN_P

  else
    {
      unsigned char *bufp = ex_info->insn_bytes + word_offset / 8;

      if (word_length > 8 * sizeof (CGEN_INSN_INT))
	abort ();

      if (fill_cache (cd, ex_info, word_offset / 8, word_length / 8, pc) == 0)
	return 0;

      value = extract_1 (cd, ex_info, start, length, word_length, bufp, pc);
    }

#endif /* ! CGEN_INT_INSN_P */

  /* Written this way to avoid undefined behaviour.  */
  mask = (((1L << (length - 1)) - 1) << 1) | 1;

  value &= mask;
  /* sign extend? */
  if (CGEN_BOOL_ATTR (attrs, CGEN_IFLD_SIGNED)
      && (value & (1L << (length - 1))))
    value |= ~mask;

  *valuep = value;

  return 1;
}

/* Default insn extractor.

   INSN_VALUE is the first base_insn_bitsize bits, translated to host order.
   The extracted fields are stored in FIELDS.
   EX_INFO is used to handle reading variable length insns.
   Return the length of the insn in bits, or 0 if no match,
   or -1 if an error occurs fetching data (memory_error_func will have
   been called).  */

static int
extract_insn_normal (CGEN_CPU_DESC cd,
		     const CGEN_INSN *insn,
		     CGEN_EXTRACT_INFO *ex_info,
		     CGEN_INSN_INT insn_value,
		     CGEN_FIELDS *fields,
		     bfd_vma pc)
{
  const CGEN_SYNTAX *syntax = CGEN_INSN_SYNTAX (insn);
  const CGEN_SYNTAX_CHAR_TYPE *syn;

  CGEN_FIELDS_BITSIZE (fields) = CGEN_INSN_BITSIZE (insn);

  CGEN_INIT_EXTRACT (cd);

  for (syn = CGEN_SYNTAX_STRING (syntax); *syn; ++syn)
    {
      int length;

      if (CGEN_SYNTAX_CHAR_P (*syn))
	continue;

      length = (* cd->extract_operand) (cd, CGEN_SYNTAX_FIELD (*syn),
					ex_info, insn_value, fields, pc);
      if (length <= 0)
	return length;
    }

  /* We recognized and successfully extracted this insn.  */
  return CGEN_INSN_BITSIZE (insn);
}

/* Machine generated code added here.  */

const char * nds32_cgen_insert_operand
  (CGEN_CPU_DESC, int, CGEN_FIELDS *, CGEN_INSN_BYTES_PTR, bfd_vma);

/* Main entry point for operand insertion.

   This function is basically just a big switch statement.  Earlier versions
   used tables to look up the function to use, but
   - if the table contains both assembler and disassembler functions then
     the disassembler contains much of the assembler and vice-versa,
   - there's a lot of inlining possibilities as things grow,
   - using a switch statement avoids the function call overhead.

   This function could be moved into `parse_insn_normal', but keeping it
   separate makes clear the interface between `parse_insn_normal' and each of
   the handlers.  It's also needed by GAS to insert operands that couldn't be
   resolved during parsing.  */

const char *
nds32_cgen_insert_operand (CGEN_CPU_DESC cd,
			     int opindex,
			     CGEN_FIELDS * fields,
			     CGEN_INSN_BYTES_PTR buffer,
			     bfd_vma pc ATTRIBUTE_UNUSED)
{
  const char * errmsg = NULL;
  unsigned int total_length = CGEN_FIELDS_BITSIZE (fields);

  switch (opindex)
    {
    case NDS32_OPERAND_AR2IDX5_A :
      errmsg = insert_normal (cd, fields->f_32_aridx5_a, 0, 0, 27, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_ARIDX4_A :
      errmsg = insert_normal (cd, fields->f_32_aridx4_a, 0, 0, 12, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_ARIDX5_A :
      errmsg = insert_normal (cd, fields->f_32_aridx5_a, 0, 0, 27, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_BITS :
      errmsg = insert_normal (cd, fields->f_16_uimm3, 0, 0, 13, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_C1_15_A :
      errmsg = insert_normal (cd, fields->f_32_c1_15_a, 0, 0, 16, 1, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_CCTLLVL :
      errmsg = insert_normal (cd, fields->f_32tx_1_21, 0, 0, 21, 1, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_CCTLST :
      errmsg = insert_normal (cd, fields->f_32t4_ext5, 0, 0, 22, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_CONCAT24 :
      errmsg = insert_normal (cd, fields->f_32_concat24, 0, 0, 8, 24, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_COPDR :
      errmsg = insert_normal (cd, fields->f_32_rt5, 0, 0, 7, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_COPWR :
      errmsg = insert_normal (cd, fields->f_32_rt5, 0, 0, 7, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_CPID :
      errmsg = insert_normal (cd, fields->f_32_2_26, 0, 0, 26, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_CPID2 :
      errmsg = insert_normal (cd, fields->f_32tx_2_17, 0, 0, 17, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_D1_A :
      errmsg = insert_normal (cd, fields->f_32_d1_a, 0, 0, 22, 1, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_DH2_16_A :
      errmsg = insert_normal (cd, fields->f_32_dh2_16_a, 0, 0, 15, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_DH2_6_A :
      errmsg = insert_normal (cd, fields->f_32_dh2_6_a, 0, 0, 25, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_DISP14 :
      {
        long value = fields->f_32t2_disp14;
        value = ((SI) (((value) - (pc))) >> (1));
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 18, 14, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_DISP16 :
      {
        long value = fields->f_32t1_disp16;
        value = ((SI) (((value) - (pc))) >> (1));
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 16, 16, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_DISP24 :
      {
        long value = fields->f_32t0_disp24;
        value = ((SI) (((value) - (pc))) >> (1));
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 8, 24, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_DISP8 :
      {
        long value = fields->f_32t1_disp8;
        value = ((SI) (((value) - (pc))) >> (1));
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 24, 8, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_DISP9 :
      {
        long value = fields->f_32t1_disp9;
        value = ((SI) (((value) - (pc))) >> (1));
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 7, 9, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_DPREFST :
      errmsg = insert_normal (cd, fields->f_32t2_st4, 0, 0, 8, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_FDRA5 :
      errmsg = insert_normal (cd, fields->f_32_ra5, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_FDRB5 :
      errmsg = insert_normal (cd, fields->f_32_rb5, 0, 0, 17, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_FDRT5 :
      errmsg = insert_normal (cd, fields->f_32_rt5, 0, 0, 7, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_FSRA5 :
      errmsg = insert_normal (cd, fields->f_32_ra5, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_FSRB5 :
      errmsg = insert_normal (cd, fields->f_32_rb5, 0, 0, 17, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_FSRT5 :
      errmsg = insert_normal (cd, fields->f_32_rt5, 0, 0, 7, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_GROUPIDX :
      errmsg = insert_normal (cd, fields->f_32_group, 0, 0, 17, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_HASH :
      break;
    case NDS32_OPERAND_HSDISP8 :
      {
        long value = fields->f_16_hsdisp8;
        value = ((SI) (((value) - (((pc) & (-2))))) >> (1));
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 8, 8, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_I2_1_A :
      errmsg = insert_normal (cd, fields->f_32_i2_1_a, 0, 0, 30, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_IM1_4_A :
      errmsg = insert_normal (cd, fields->f_32_im1_4_a, 0, 0, 27, 1, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_IM5_I_A :
      {
{
  FLD (f_32_im1_4_a) = ((UINT) (FLD (f_32_im5_i_a)) >> (2));
  FLD (f_32_i2_1_a) = ((FLD (f_32_im5_i_a)) & (3));
}
        errmsg = insert_normal (cd, fields->f_32_im1_4_a, 0, 0, 27, 1, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_i2_1_a, 0, 0, 30, 2, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_IM5_M_A :
      {
{
if((FLD(f_32_im5_m_a) >> 2) == FLD(f_32_im1_4_a)) {
  FLD (f_32_m2_3_a) = ((FLD (f_32_im5_m_a)) & (3));
} else {
static char msg[100];
sprintf(msg, "invalid (Ip,Mr) pair");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_im1_4_a, 0, 0, 27, 1, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_m2_3_a, 0, 0, 28, 2, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_IM6_I_0_A :
      {
  FLD (f_32_i2_1_a) = FLD (f_32_im6_i_0_a);
        errmsg = insert_normal (cd, fields->f_32_i2_1_a, 0, 0, 30, 2, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_IM6_I_1_A :
      {
{
if((FLD(f_32_im6_i_1_a) & 0x3) != FLD(f_32_i2_1_a)) {
static char msg[100];
sprintf(msg, "invalid (Ip,Iq) pair");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_i2_1_a, 0, 0, 30, 2, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_IM6_M_0_A :
      {
  FLD (f_32_m2_3_a) = FLD (f_32_im6_m_0_a);
        errmsg = insert_normal (cd, fields->f_32_m2_3_a, 0, 0, 28, 2, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_IM6_M_1_A :
      {
  FLD (f_32_m2_5_a) = ((FLD (f_32_im6_m_1_a)) & (3));
        errmsg = insert_normal (cd, fields->f_32_m2_5_a, 0, 0, 26, 2, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_IMM16_A :
      errmsg = insert_normal (cd, fields->f_32_imm16_a, 0, 0, 16, 16, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_IMM5U :
      errmsg = insert_normal (cd, fields->f_16_uimm5, 0, 0, 11, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_LSBLOC_A :
      errmsg = insert_normal (cd, fields->f_32_lsbloc_a, 0, 0, 27, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_M2_3_A :
      errmsg = insert_normal (cd, fields->f_32_m2_3_a, 0, 0, 28, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_M2_5_A :
      errmsg = insert_normal (cd, fields->f_32_m2_5_a, 0, 0, 26, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_MASK4 :
      errmsg = insert_normal (cd, fields->f_32t5_mask4, 0, 0, 22, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_MFUSRIDX :
      {
{
  FLD (f_32_group) = ((UINT) (FLD (f_32_group_usr)) >> (5));
  FLD (f_32_usr) = ((FLD (f_32_group_usr)) & (31));
}
        errmsg = insert_normal (cd, fields->f_32_group, 0, 0, 17, 5, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_usr, 0, 0, 12, 5, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_MSYNCST :
      errmsg = insert_normal (cd, fields->f_32t3_ext3, 0, 0, 24, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_MTUSRIDX :
      {
{
  FLD (f_32_group) = ((UINT) (FLD (f_32_group_usr)) >> (5));
  FLD (f_32_usr) = ((FLD (f_32_group_usr)) & (31));
}
        errmsg = insert_normal (cd, fields->f_32_group, 0, 0, 17, 5, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_usr, 0, 0, 12, 5, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10A5_A :
      {
  FLD (f_32_ra4_19_a) = FLD (f_32_r10a5_a);
        errmsg = insert_normal (cd, fields->f_32_ra4_19_a, 0, 0, 12, 4, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10A5_A_B :
      {
  FLD (f_32_ra4_19_a) = FLD (f_32_r10a5_a);
        errmsg = insert_normal (cd, fields->f_32_ra4_19_a, 0, 0, 12, 4, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10A5_A_T :
      {
  FLD (f_32_ra4_19_a) = FLD (f_32_r10a5_a);
        errmsg = insert_normal (cd, fields->f_32_ra4_19_a, 0, 0, 12, 4, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10B5_A :
      {
{
  FLD (f_32_c1_15_a) = ((UINT) (FLD (f_32_r10b5_a)) >> (3));
  FLD (f_32_rb3_14_a) = ((FLD (f_32_r10b5_a)) & (7));
}
        errmsg = insert_normal (cd, fields->f_32_c1_15_a, 0, 0, 16, 1, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_rb3_14_a, 0, 0, 17, 3, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10B5_A_B :
      {
{
  FLD (f_32_c1_15_a) = ((UINT) (FLD (f_32_r10b5_a)) >> (3));
  FLD (f_32_rb3_14_a) = ((FLD (f_32_r10b5_a)) & (7));
}
        errmsg = insert_normal (cd, fields->f_32_c1_15_a, 0, 0, 16, 1, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_rb3_14_a, 0, 0, 17, 3, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10B5_A_T :
      {
{
  FLD (f_32_c1_15_a) = ((UINT) (FLD (f_32_r10b5_a)) >> (3));
  FLD (f_32_rb3_14_a) = ((FLD (f_32_r10b5_a)) & (7));
}
        errmsg = insert_normal (cd, fields->f_32_c1_15_a, 0, 0, 16, 1, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_rb3_14_a, 0, 0, 17, 3, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10C5_0_A :
      {
{
if((FLD(f_32_r10c5_0_a) >> 3) == FLD(f_32_c1_15_a)) {
  FLD (f_32_rc2_11_a) = ((((UINT) (FLD (f_32_r10c5_0_a)) >> (1))) & (3));
} else {
static char msg[100];
sprintf(msg, "invalid (Rb,Rte/Rte+1) pair");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_c1_15_a, 0, 0, 16, 1, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_rc2_11_a, 0, 0, 20, 2, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10C5_1_A :
      {
{
if((FLD(f_32_r10c5_1_a) >> 1) != ((FLD(f_32_c1_15_a) << 2) | FLD(f_32_rc2_11_a))) {
static char msg[100];
sprintf(msg, "Rte+1 index does not equal Rte index plus 1");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_c1_15_a, 0, 0, 16, 1, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_rc2_11_a, 0, 0, 20, 2, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_R10C5_A :
      {
{
if((FLD(f_32_r10c5_a) >> 3) == FLD(f_32_c1_15_a)) {
  FLD (f_32_rc2_11_a) = ((((UINT) (FLD (f_32_r10c5_a)) >> (1))) & (3));
  FLD (f_32_rc1_5_a) = ((FLD (f_32_r10c5_a)) & (1));
} else {
static char msg[100];
sprintf(msg, "invalid (Rb,Rt) pair");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_c1_15_a, 0, 0, 16, 1, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_rc2_11_a, 0, 0, 20, 2, 32, total_length, buffer);
        if (errmsg)
          break;
        errmsg = insert_normal (cd, fields->f_32_rc1_5_a, 0, 0, 26, 1, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_RA3 :
      errmsg = insert_normal (cd, fields->f_16_ra3, 0, 0, 10, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RA4 :
      errmsg = insert_normal (cd, fields->f_16_ra4, 0, 0, 7, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RA4_19_A :
      errmsg = insert_normal (cd, fields->f_32_ra4_19_a, 0, 0, 12, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RA5 :
      errmsg = insert_normal (cd, fields->f_32_ra5, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RA5_A :
      errmsg = insert_normal (cd, fields->f_32_ra5_a, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RA5_A_B :
      errmsg = insert_normal (cd, fields->f_32_ra5_a, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RA5_A_T :
      errmsg = insert_normal (cd, fields->f_32_ra5_a, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RA5E :
      errmsg = insert_normal (cd, fields->f_16_ra5e, 0, 0, 12, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RA5H :
      errmsg = insert_normal (cd, fields->f_16_ra5h, 0, 0, 11, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RB3 :
      errmsg = insert_normal (cd, fields->f_16_rb3, 0, 0, 13, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RB3_14_A :
      errmsg = insert_normal (cd, fields->f_32_rb3_14_a, 0, 0, 17, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RB5 :
      errmsg = insert_normal (cd, fields->f_32_rb5, 0, 0, 17, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RB5_A :
      errmsg = insert_normal (cd, fields->f_32_rb5_a, 0, 0, 17, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RB5_A_B :
      errmsg = insert_normal (cd, fields->f_32_rb5_a, 0, 0, 17, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RB5_A_T :
      errmsg = insert_normal (cd, fields->f_32_rb5_a, 0, 0, 17, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RB5H :
      errmsg = insert_normal (cd, fields->f_16_rb5h, 0, 0, 11, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RB5P_A :
      {
{
if(FLD(f_32_rb5p_a) != FLD(f_32_ra5_a)) {
  FLD (f_32_rb5_a) = FLD (f_32_rb5p_a);
} else {
static char msg[100];
sprintf(msg, "destination registers cannot be the same");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_rb5_a, 0, 0, 17, 5, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_RB5P_A_B :
      {
{
if(FLD(f_32_rb5p_a) != FLD(f_32_ra5_a)) {
  FLD (f_32_rb5_a) = FLD (f_32_rb5p_a);
} else {
static char msg[100];
sprintf(msg, "destination registers cannot be the same");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_rb5_a, 0, 0, 17, 5, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_RB5P_A_T :
      {
{
if(FLD(f_32_rb5p_a) != FLD(f_32_ra5_a)) {
  FLD (f_32_rb5_a) = FLD (f_32_rb5p_a);
} else {
static char msg[100];
sprintf(msg, "destination registers cannot be the same");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_rb5_a, 0, 0, 17, 5, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_RC1_5_A :
      errmsg = insert_normal (cd, fields->f_32_rc1_5_a, 0, 0, 26, 1, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RC2_11_A :
      errmsg = insert_normal (cd, fields->f_32_rc2_11_a, 0, 0, 20, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RC4_A :
      errmsg = insert_normal (cd, fields->f_32_rc4_a, 0, 0, 22, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RC5_0_A :
      {
  FLD (f_32_rc4_a) = ((UINT) (FLD (f_32_rc5_0_a)) >> (1));
        errmsg = insert_normal (cd, fields->f_32_rc4_a, 0, 0, 22, 4, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_RC5_1_A :
      {
{
if((FLD(f_32_rc5_1_a) >> 1) != FLD(f_32_rc4_a)) {
static char msg[100];
sprintf(msg, "Rte+1 index does not equal Rte index plus 1");
errmsg = msg;
break;}}
        errmsg = insert_normal (cd, fields->f_32_rc4_a, 0, 0, 22, 4, 32, total_length, buffer);
        if (errmsg)
          break;
      }
      break;
    case NDS32_OPERAND_RD1 :
      errmsg = insert_normal (cd, fields->f_32_rd1, 0, 0, 10, 1, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RD1HL :
      errmsg = insert_normal (cd, fields->f_32_rd1hl, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RD5_A :
      errmsg = insert_normal (cd, fields->f_32_rd5_a, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_REGLIST :
      errmsg = insert_normal (cd, fields->f_16_mask2, 0, 0, 9, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RS5 :
      errmsg = insert_normal (cd, fields->f_32_rs5, 0, 0, 22, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RT3 :
      errmsg = insert_normal (cd, fields->f_16_rt3, 0, 0, 5, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RT3_7 :
      errmsg = insert_normal (cd, fields->f_16_rt3_7, 0, 0, 7, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RT3E5 :
      errmsg = insert_normal (cd, fields->f_16_rt3, 0, 0, 5, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RT4 :
      errmsg = insert_normal (cd, fields->f_16_rt4, 0, 0, 7, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RT5 :
      errmsg = insert_normal (cd, fields->f_32_rt5, 0, 0, 7, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RT5E :
      errmsg = insert_normal (cd, fields->f_16_rt5e, 0, 0, 8, 4, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RT5H :
      errmsg = insert_normal (cd, fields->f_16_rt5h, 0, 0, 6, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RTH5 :
      errmsg = insert_normal (cd, fields->f_32_rt5, 0, 0, 7, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_RTL5 :
      errmsg = insert_normal (cd, fields->f_32_ra5, 0, 0, 12, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SI :
      errmsg = insert_normal (cd, fields->f_32t3_sub10si, 0, 0, 22, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SIMM10 :
      errmsg = insert_normal (cd, fields->f_16_simm10, 0|(1<<CGEN_IFLD_SIGNED), 0, 6, 10, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SIMM11 :
      errmsg = insert_normal (cd, fields->f_32t2_simm11, 0|(1<<CGEN_IFLD_SIGNED), 0, 13, 11, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SIMM5H :
      errmsg = insert_normal (cd, fields->f_16_simm5, 0|(1<<CGEN_IFLD_SIGNED), 0, 11, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SIMM5W :
      {
        long value = fields->f_16_simm5w;
        value = value; if (value&0x3) return BAD_WOFFSET; else if (value>-4 || value <-128) return BAD_RANGEOFFSET; else value = (128+value) >> 2;
        errmsg = insert_normal (cd, value, 0, 0, 11, 5, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SLO12D :
      {
        long value = fields->f_32tx_slo12d;
        value = value; if (value&0x3) return BAD_WOFFSET; else value>>=2;
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED), 0, 20, 12, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SLO12W :
      {
        long value = fields->f_32tx_slo12w;
        value = value; if (value&0x3) return BAD_WOFFSET; else value>>=2;
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED), 0, 20, 12, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SLO15 :
      errmsg = insert_normal (cd, fields->f_32t2_slo15b, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SLO15B :
      errmsg = insert_normal (cd, fields->f_32t2_slo15b, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SLO15D :
      {
        long value = fields->f_32t2_slo15d;
        value = value; if (value&0x7) return BAD_DWOFFSET; else value>>=3;
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SLO15H :
      {
        long value = fields->f_32t2_slo15h;
        value = value; if (value&0x1) return BAD_HWOFFSET; else value>>=1;
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SLO15W :
      {
        long value = fields->f_32t2_slo15w;
        value = value; if (value&0x3) return BAD_WOFFSET; else value>>=2;
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SLO17W :
      {
        long value = fields->f_32_slo17w;
        value = value; if (value&0x3) return BAD_WOFFSET; else value>>=2;
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED), 0, 15, 17, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SLO18H :
      {
        long value = fields->f_32_slo18h;
        value = value; if (value&0x1) return BAD_HWOFFSET; else value>>=1;
        errmsg = insert_normal (cd, value, 0|(1<<CGEN_IFLD_SIGNED), 0, 14, 18, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SLO19 :
      errmsg = insert_normal (cd, fields->f_32_slo19, 0|(1<<CGEN_IFLD_SIGNED), 0, 13, 19, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SLO20 :
      errmsg = insert_normal (cd, fields->f_32t1_slo20, 0|(1<<CGEN_IFLD_SIGNED), 0, 12, 20, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SR10 :
      errmsg = insert_normal (cd, fields->f_32_sr10, 0, 0, 12, 10, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_STANDBYST :
      errmsg = insert_normal (cd, fields->f_32t4_ext2, 0, 0, 25, 2, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SUIMM5 :
      {
        long value = fields->f_16_suimm5;
        value = value; if (value<=47 && value>=16) value = value - 16; else return BAD_SHIFTOFFSET;
        errmsg = insert_normal (cd, value, 0, 0, 11, 5, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_SWID15 :
      errmsg = insert_normal (cd, fields->f_32t3_swid15, 0, 0, 12, 15, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SWID5 :
      errmsg = insert_normal (cd, fields->f_16_swid5, 0, 0, 11, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_SWID9 :
      errmsg = insert_normal (cd, fields->f_16_swid9, 0, 0, 7, 9, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_TLBOPST :
      errmsg = insert_normal (cd, fields->f_32t4_ext5, 0, 0, 22, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UHI20 :
      errmsg = insert_normal (cd, fields->f_32t1_uhi20, 0, 0, 12, 20, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UIMM12 :
      errmsg = insert_normal (cd, fields->f_32_12_12, 0, 0, 12, 12, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UIMM19 :
      errmsg = insert_normal (cd, fields->f_32_19_7, 0, 0, 7, 19, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UIMM3 :
      errmsg = insert_normal (cd, fields->f_16_uimm3, 0, 0, 13, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UIMM3_10 :
      errmsg = insert_normal (cd, fields->f_16_uimm3_10, 0, 0, 10, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UIMM5 :
      errmsg = insert_normal (cd, fields->f_32t3_uimm5, 0, 0, 17, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UIMM5D :
      {
        long value = fields->f_16_uimm5d;
        value = value; if (value&0x7) return BAD_DWOFFSET; else value>>=3;
        errmsg = insert_normal (cd, value, 0, 0, 11, 5, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_UIMM5H :
      errmsg = insert_normal (cd, fields->f_16_uimm5, 0, 0, 11, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UIMM6W :
      {
        long value = fields->f_16_uimm6w;
        value = value; if (value&0x3) return BAD_WOFFSET; else value>>=2;
        errmsg = insert_normal (cd, value, 0, 0, 10, 6, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_UIMM8_S :
      errmsg = insert_normal (cd, fields->f_32_uimm8_s, 0, 0, 17, 8, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_UIMM_SR10 :
      errmsg = insert_normal (cd, fields->f_32_sr10, 0, 0, 12, 10, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_ULO15 :
      errmsg = insert_normal (cd, fields->f_32t2_ulo15b, 0, 0, 17, 15, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_ULO15B :
      errmsg = insert_normal (cd, fields->f_32t2_ulo15b, 0, 0, 17, 15, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_ULO15D :
      {
        long value = fields->f_32t2_ulo15d;
        value = value; if (value&0x7) return BAD_DWOFFSET; else value>>=3;
        errmsg = insert_normal (cd, value, 0, 0, 17, 15, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_ULO15H :
      {
        long value = fields->f_32t2_ulo15h;
        value = value; if (value&0x1) return BAD_HWOFFSET; else value>>=1;
        errmsg = insert_normal (cd, value, 0, 0, 17, 15, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_ULO15W :
      {
        long value = fields->f_32t2_ulo15w;
        value = value; if (value&0x3) return BAD_WOFFSET; else value>>=2;
        errmsg = insert_normal (cd, value, 0, 0, 17, 15, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_ULO3B :
      errmsg = insert_normal (cd, fields->f_16_ulo3b, 0, 0, 13, 3, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_ULO3H :
      {
        long value = fields->f_16_ulo3h;
        value = value; if (value&0x1) return BAD_WOFFSET; else value>>=1;
        errmsg = insert_normal (cd, value, 0, 0, 13, 3, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_ULO3W :
      {
        long value = fields->f_16_ulo3w;
        value = value; if (value&0x3) return BAD_WOFFSET; else value>>=2;
        errmsg = insert_normal (cd, value, 0, 0, 13, 3, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_ULO5 :
      errmsg = insert_normal (cd, fields->f_32t21_ulo5, 0, 0, 22, 5, 32, total_length, buffer);
      break;
    case NDS32_OPERAND_ULO7W :
      {
        long value = fields->f_16_ulo7w;
        value = value; if (value&0x3) return BAD_WOFFSET; else value>>=2;
        errmsg = insert_normal (cd, value, 0, 0, 9, 7, 32, total_length, buffer);
      }
      break;
    case NDS32_OPERAND_USRIDX :
      errmsg = insert_normal (cd, fields->f_32_usr, 0, 0, 12, 5, 32, total_length, buffer);
      break;

    default :
      /* xgettext:c-format */
      fprintf (stderr, _("Unrecognized field %d while building insn.\n"),
	       opindex);
      abort ();
  }

  return errmsg;
}

int nds32_cgen_extract_operand
  (CGEN_CPU_DESC, int, CGEN_EXTRACT_INFO *, CGEN_INSN_INT, CGEN_FIELDS *, bfd_vma);

/* Main entry point for operand extraction.
   The result is <= 0 for error, >0 for success.
   ??? Actual values aren't well defined right now.

   This function is basically just a big switch statement.  Earlier versions
   used tables to look up the function to use, but
   - if the table contains both assembler and disassembler functions then
     the disassembler contains much of the assembler and vice-versa,
   - there's a lot of inlining possibilities as things grow,
   - using a switch statement avoids the function call overhead.

   This function could be moved into `print_insn_normal', but keeping it
   separate makes clear the interface between `print_insn_normal' and each of
   the handlers.  */

int
nds32_cgen_extract_operand (CGEN_CPU_DESC cd,
			     int opindex,
			     CGEN_EXTRACT_INFO *ex_info,
			     CGEN_INSN_INT insn_value,
			     CGEN_FIELDS * fields,
			     bfd_vma pc)
{
  /* Assume success (for those operands that are nops).  */
  int length = 1;
  unsigned int total_length = CGEN_FIELDS_BITSIZE (fields);

  switch (opindex)
    {
    case NDS32_OPERAND_AR2IDX5_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 27, 5, 32, total_length, pc, & fields->f_32_aridx5_a);
      break;
    case NDS32_OPERAND_ARIDX4_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 4, 32, total_length, pc, & fields->f_32_aridx4_a);
      break;
    case NDS32_OPERAND_ARIDX5_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 27, 5, 32, total_length, pc, & fields->f_32_aridx5_a);
      break;
    case NDS32_OPERAND_BITS :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 13, 3, 32, total_length, pc, & fields->f_16_uimm3);
      break;
    case NDS32_OPERAND_C1_15_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 16, 1, 32, total_length, pc, & fields->f_32_c1_15_a);
      break;
    case NDS32_OPERAND_CCTLLVL :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 21, 1, 32, total_length, pc, & fields->f_32tx_1_21);
      break;
    case NDS32_OPERAND_CCTLST :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 5, 32, total_length, pc, & fields->f_32t4_ext5);
      break;
    case NDS32_OPERAND_CONCAT24 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 8, 24, 32, total_length, pc, & fields->f_32_concat24);
      break;
    case NDS32_OPERAND_COPDR :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 5, 32, total_length, pc, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_COPWR :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 5, 32, total_length, pc, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_CPID :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 26, 2, 32, total_length, pc, & fields->f_32_2_26);
      break;
    case NDS32_OPERAND_CPID2 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 2, 32, total_length, pc, & fields->f_32tx_2_17);
      break;
    case NDS32_OPERAND_D1_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 1, 32, total_length, pc, & fields->f_32_d1_a);
      break;
    case NDS32_OPERAND_DH2_16_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 15, 2, 32, total_length, pc, & fields->f_32_dh2_16_a);
      break;
    case NDS32_OPERAND_DH2_6_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 25, 2, 32, total_length, pc, & fields->f_32_dh2_6_a);
      break;
    case NDS32_OPERAND_DISP14 :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 18, 14, 32, total_length, pc, & value);
        value = ((((value) << (1))) + (pc));
        fields->f_32t2_disp14 = value;
      }
      break;
    case NDS32_OPERAND_DISP16 :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 16, 16, 32, total_length, pc, & value);
        value = ((((value) << (1))) + (pc));
        fields->f_32t1_disp16 = value;
      }
      break;
    case NDS32_OPERAND_DISP24 :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 8, 24, 32, total_length, pc, & value);
        value = ((((value) << (1))) + (pc));
        fields->f_32t0_disp24 = value;
      }
      break;
    case NDS32_OPERAND_DISP8 :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 24, 8, 32, total_length, pc, & value);
        value = ((((value) << (1))) + (pc));
        fields->f_32t1_disp8 = value;
      }
      break;
    case NDS32_OPERAND_DISP9 :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 7, 9, 32, total_length, pc, & value);
        value = ((((value) << (1))) + (pc));
        fields->f_32t1_disp9 = value;
      }
      break;
    case NDS32_OPERAND_DPREFST :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 8, 4, 32, total_length, pc, & fields->f_32t2_st4);
      break;
    case NDS32_OPERAND_FDRA5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_ra5);
      break;
    case NDS32_OPERAND_FDRB5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5);
      break;
    case NDS32_OPERAND_FDRT5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 5, 32, total_length, pc, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_FSRA5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_ra5);
      break;
    case NDS32_OPERAND_FSRB5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5);
      break;
    case NDS32_OPERAND_FSRT5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 5, 32, total_length, pc, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_GROUPIDX :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_group);
      break;
    case NDS32_OPERAND_HASH :
      break;
    case NDS32_OPERAND_HSDISP8 :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED)|(1<<CGEN_IFLD_RELOC)|(1<<CGEN_IFLD_PCREL_ADDR), 0, 8, 8, 32, total_length, pc, & value);
        value = ((((value) << (1))) + (((pc) & (-2))));
        fields->f_16_hsdisp8 = value;
      }
      break;
    case NDS32_OPERAND_I2_1_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 30, 2, 32, total_length, pc, & fields->f_32_i2_1_a);
      break;
    case NDS32_OPERAND_IM1_4_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 27, 1, 32, total_length, pc, & fields->f_32_im1_4_a);
      break;
    case NDS32_OPERAND_IM5_I_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 27, 1, 32, total_length, pc, & fields->f_32_im1_4_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 30, 2, 32, total_length, pc, & fields->f_32_i2_1_a);
        if (length <= 0) break;
  FLD (f_32_im5_i_a) = ((((FLD (f_32_im1_4_a)) << (2))) | (FLD (f_32_i2_1_a)));
      }
      break;
    case NDS32_OPERAND_IM5_M_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 27, 1, 32, total_length, pc, & fields->f_32_im1_4_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 28, 2, 32, total_length, pc, & fields->f_32_m2_3_a);
        if (length <= 0) break;
  FLD (f_32_im5_m_a) = ((((FLD (f_32_im1_4_a)) << (2))) | (FLD (f_32_m2_3_a)));
      }
      break;
    case NDS32_OPERAND_IM6_I_0_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 30, 2, 32, total_length, pc, & fields->f_32_i2_1_a);
        if (length <= 0) break;
  FLD (f_32_im6_i_0_a) = FLD (f_32_i2_1_a);
      }
      break;
    case NDS32_OPERAND_IM6_I_1_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 30, 2, 32, total_length, pc, & fields->f_32_i2_1_a);
        if (length <= 0) break;
  FLD (f_32_im6_i_1_a) = ((FLD (f_32_i2_1_a)) | (4));
      }
      break;
    case NDS32_OPERAND_IM6_M_0_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 28, 2, 32, total_length, pc, & fields->f_32_m2_3_a);
        if (length <= 0) break;
  FLD (f_32_im6_m_0_a) = FLD (f_32_m2_3_a);
      }
      break;
    case NDS32_OPERAND_IM6_M_1_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 26, 2, 32, total_length, pc, & fields->f_32_m2_5_a);
        if (length <= 0) break;
  FLD (f_32_im6_m_1_a) = ((FLD (f_32_m2_5_a)) | (4));
      }
      break;
    case NDS32_OPERAND_IMM16_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 16, 16, 32, total_length, pc, & fields->f_32_imm16_a);
      break;
    case NDS32_OPERAND_IMM5U :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 11, 5, 32, total_length, pc, & fields->f_16_uimm5);
      break;
    case NDS32_OPERAND_LSBLOC_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 27, 5, 32, total_length, pc, & fields->f_32_lsbloc_a);
      break;
    case NDS32_OPERAND_M2_3_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 28, 2, 32, total_length, pc, & fields->f_32_m2_3_a);
      break;
    case NDS32_OPERAND_M2_5_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 26, 2, 32, total_length, pc, & fields->f_32_m2_5_a);
      break;
    case NDS32_OPERAND_MASK4 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 4, 32, total_length, pc, & fields->f_32t5_mask4);
      break;
    case NDS32_OPERAND_MFUSRIDX :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_group);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_usr);
        if (length <= 0) break;
  FLD (f_32_group_usr) = ((((FLD (f_32_group)) << (5))) | (FLD (f_32_usr)));
      }
      break;
    case NDS32_OPERAND_MSYNCST :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 24, 3, 32, total_length, pc, & fields->f_32t3_ext3);
      break;
    case NDS32_OPERAND_MTUSRIDX :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_group);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_usr);
        if (length <= 0) break;
  FLD (f_32_group_usr) = ((((FLD (f_32_group)) << (5))) | (FLD (f_32_usr)));
      }
      break;
    case NDS32_OPERAND_R10A5_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 4, 32, total_length, pc, & fields->f_32_ra4_19_a);
        if (length <= 0) break;
  FLD (f_32_r10a5_a) = FLD (f_32_ra4_19_a);
      }
      break;
    case NDS32_OPERAND_R10A5_A_B :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 4, 32, total_length, pc, & fields->f_32_ra4_19_a);
        if (length <= 0) break;
  FLD (f_32_r10a5_a) = FLD (f_32_ra4_19_a);
      }
      break;
    case NDS32_OPERAND_R10A5_A_T :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 4, 32, total_length, pc, & fields->f_32_ra4_19_a);
        if (length <= 0) break;
  FLD (f_32_r10a5_a) = FLD (f_32_ra4_19_a);
      }
      break;
    case NDS32_OPERAND_R10B5_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 16, 1, 32, total_length, pc, & fields->f_32_c1_15_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 3, 32, total_length, pc, & fields->f_32_rb3_14_a);
        if (length <= 0) break;
  FLD (f_32_r10b5_a) = ((((FLD (f_32_c1_15_a)) << (3))) | (FLD (f_32_rb3_14_a)));
      }
      break;
    case NDS32_OPERAND_R10B5_A_B :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 16, 1, 32, total_length, pc, & fields->f_32_c1_15_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 3, 32, total_length, pc, & fields->f_32_rb3_14_a);
        if (length <= 0) break;
  FLD (f_32_r10b5_a) = ((((FLD (f_32_c1_15_a)) << (3))) | (FLD (f_32_rb3_14_a)));
      }
      break;
    case NDS32_OPERAND_R10B5_A_T :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 16, 1, 32, total_length, pc, & fields->f_32_c1_15_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 3, 32, total_length, pc, & fields->f_32_rb3_14_a);
        if (length <= 0) break;
  FLD (f_32_r10b5_a) = ((((FLD (f_32_c1_15_a)) << (3))) | (FLD (f_32_rb3_14_a)));
      }
      break;
    case NDS32_OPERAND_R10C5_0_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 16, 1, 32, total_length, pc, & fields->f_32_c1_15_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 20, 2, 32, total_length, pc, & fields->f_32_rc2_11_a);
        if (length <= 0) break;
  FLD (f_32_r10c5_0_a) = ((((FLD (f_32_c1_15_a)) << (3))) | (((FLD (f_32_rc2_11_a)) << (1))));
      }
      break;
    case NDS32_OPERAND_R10C5_1_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 16, 1, 32, total_length, pc, & fields->f_32_c1_15_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 20, 2, 32, total_length, pc, & fields->f_32_rc2_11_a);
        if (length <= 0) break;
  FLD (f_32_r10c5_1_a) = ((((((FLD (f_32_c1_15_a)) << (3))) | (((FLD (f_32_rc2_11_a)) << (1))))) | (1));
      }
      break;
    case NDS32_OPERAND_R10C5_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 16, 1, 32, total_length, pc, & fields->f_32_c1_15_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 20, 2, 32, total_length, pc, & fields->f_32_rc2_11_a);
        if (length <= 0) break;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 26, 1, 32, total_length, pc, & fields->f_32_rc1_5_a);
        if (length <= 0) break;
  FLD (f_32_r10c5_a) = ((((((FLD (f_32_c1_15_a)) << (3))) | (((FLD (f_32_rc2_11_a)) << (1))))) | (FLD (f_32_rc1_5_a)));
      }
      break;
    case NDS32_OPERAND_RA3 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 10, 3, 32, total_length, pc, & fields->f_16_ra3);
      break;
    case NDS32_OPERAND_RA4 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 4, 32, total_length, pc, & fields->f_16_ra4);
      break;
    case NDS32_OPERAND_RA4_19_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 4, 32, total_length, pc, & fields->f_32_ra4_19_a);
      break;
    case NDS32_OPERAND_RA5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_ra5);
      break;
    case NDS32_OPERAND_RA5_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_ra5_a);
      break;
    case NDS32_OPERAND_RA5_A_B :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_ra5_a);
      break;
    case NDS32_OPERAND_RA5_A_T :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_ra5_a);
      break;
    case NDS32_OPERAND_RA5E :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 4, 32, total_length, pc, & fields->f_16_ra5e);
      break;
    case NDS32_OPERAND_RA5H :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 11, 5, 32, total_length, pc, & fields->f_16_ra5h);
      break;
    case NDS32_OPERAND_RB3 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 13, 3, 32, total_length, pc, & fields->f_16_rb3);
      break;
    case NDS32_OPERAND_RB3_14_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 3, 32, total_length, pc, & fields->f_32_rb3_14_a);
      break;
    case NDS32_OPERAND_RB5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5);
      break;
    case NDS32_OPERAND_RB5_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5_a);
      break;
    case NDS32_OPERAND_RB5_A_B :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5_a);
      break;
    case NDS32_OPERAND_RB5_A_T :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5_a);
      break;
    case NDS32_OPERAND_RB5H :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 11, 5, 32, total_length, pc, & fields->f_16_rb5h);
      break;
    case NDS32_OPERAND_RB5P_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5_a);
        if (length <= 0) break;
  FLD (f_32_rb5p_a) = FLD (f_32_rb5_a);
      }
      break;
    case NDS32_OPERAND_RB5P_A_B :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5_a);
        if (length <= 0) break;
  FLD (f_32_rb5p_a) = FLD (f_32_rb5_a);
      }
      break;
    case NDS32_OPERAND_RB5P_A_T :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32_rb5_a);
        if (length <= 0) break;
  FLD (f_32_rb5p_a) = FLD (f_32_rb5_a);
      }
      break;
    case NDS32_OPERAND_RC1_5_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 26, 1, 32, total_length, pc, & fields->f_32_rc1_5_a);
      break;
    case NDS32_OPERAND_RC2_11_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 20, 2, 32, total_length, pc, & fields->f_32_rc2_11_a);
      break;
    case NDS32_OPERAND_RC4_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 4, 32, total_length, pc, & fields->f_32_rc4_a);
      break;
    case NDS32_OPERAND_RC5_0_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 4, 32, total_length, pc, & fields->f_32_rc4_a);
        if (length <= 0) break;
  FLD (f_32_rc5_0_a) = ((FLD (f_32_rc4_a)) << (1));
      }
      break;
    case NDS32_OPERAND_RC5_1_A :
      {
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 4, 32, total_length, pc, & fields->f_32_rc4_a);
        if (length <= 0) break;
  FLD (f_32_rc5_1_a) = ((((FLD (f_32_rc4_a)) << (1))) | (1));
      }
      break;
    case NDS32_OPERAND_RD1 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 10, 1, 32, total_length, pc, & fields->f_32_rd1);
      break;
    case NDS32_OPERAND_RD1HL :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_rd1hl);
      break;
    case NDS32_OPERAND_RD5_A :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_rd5_a);
      break;
    case NDS32_OPERAND_REGLIST :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 9, 2, 32, total_length, pc, & fields->f_16_mask2);
      break;
    case NDS32_OPERAND_RS5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 5, 32, total_length, pc, & fields->f_32_rs5);
      break;
    case NDS32_OPERAND_RT3 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 5, 3, 32, total_length, pc, & fields->f_16_rt3);
      break;
    case NDS32_OPERAND_RT3_7 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 3, 32, total_length, pc, & fields->f_16_rt3_7);
      break;
    case NDS32_OPERAND_RT3E5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 5, 3, 32, total_length, pc, & fields->f_16_rt3);
      break;
    case NDS32_OPERAND_RT4 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 4, 32, total_length, pc, & fields->f_16_rt4);
      break;
    case NDS32_OPERAND_RT5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 5, 32, total_length, pc, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_RT5E :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 8, 4, 32, total_length, pc, & fields->f_16_rt5e);
      break;
    case NDS32_OPERAND_RT5H :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 6, 5, 32, total_length, pc, & fields->f_16_rt5h);
      break;
    case NDS32_OPERAND_RTH5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 5, 32, total_length, pc, & fields->f_32_rt5);
      break;
    case NDS32_OPERAND_RTL5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_ra5);
      break;
    case NDS32_OPERAND_SI :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 2, 32, total_length, pc, & fields->f_32t3_sub10si);
      break;
    case NDS32_OPERAND_SIMM10 :
      length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 6, 10, 32, total_length, pc, & fields->f_16_simm10);
      break;
    case NDS32_OPERAND_SIMM11 :
      length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 13, 11, 32, total_length, pc, & fields->f_32t2_simm11);
      break;
    case NDS32_OPERAND_SIMM5H :
      length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 11, 5, 32, total_length, pc, & fields->f_16_simm5);
      break;
    case NDS32_OPERAND_SIMM5W :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 11, 5, 32, total_length, pc, & value);
        value = ((((value) - (32))) << (2));
        fields->f_16_simm5w = value;
      }
      break;
    case NDS32_OPERAND_SLO12D :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 20, 12, 32, total_length, pc, & value);
        value = ((value) << (2));
        fields->f_32tx_slo12d = value;
      }
      break;
    case NDS32_OPERAND_SLO12W :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 20, 12, 32, total_length, pc, & value);
        value = ((value) << (2));
        fields->f_32tx_slo12w = value;
      }
      break;
    case NDS32_OPERAND_SLO15 :
      length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, pc, & fields->f_32t2_slo15b);
      break;
    case NDS32_OPERAND_SLO15B :
      length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, pc, & fields->f_32t2_slo15b);
      break;
    case NDS32_OPERAND_SLO15D :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, pc, & value);
        value = ((value) << (3));
        fields->f_32t2_slo15d = value;
      }
      break;
    case NDS32_OPERAND_SLO15H :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, pc, & value);
        value = ((value) << (1));
        fields->f_32t2_slo15h = value;
      }
      break;
    case NDS32_OPERAND_SLO15W :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 17, 15, 32, total_length, pc, & value);
        value = ((value) << (2));
        fields->f_32t2_slo15w = value;
      }
      break;
    case NDS32_OPERAND_SLO17W :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 15, 17, 32, total_length, pc, & value);
        value = ((value) << (2));
        fields->f_32_slo17w = value;
      }
      break;
    case NDS32_OPERAND_SLO18H :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 14, 18, 32, total_length, pc, & value);
        value = ((value) << (1));
        fields->f_32_slo18h = value;
      }
      break;
    case NDS32_OPERAND_SLO19 :
      length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 13, 19, 32, total_length, pc, & fields->f_32_slo19);
      break;
    case NDS32_OPERAND_SLO20 :
      length = extract_normal (cd, ex_info, insn_value, 0|(1<<CGEN_IFLD_SIGNED), 0, 12, 20, 32, total_length, pc, & fields->f_32t1_slo20);
      break;
    case NDS32_OPERAND_SR10 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 10, 32, total_length, pc, & fields->f_32_sr10);
      break;
    case NDS32_OPERAND_STANDBYST :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 25, 2, 32, total_length, pc, & fields->f_32t4_ext2);
      break;
    case NDS32_OPERAND_SUIMM5 :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 11, 5, 32, total_length, pc, & value);
        value = ((value) + (16));
        fields->f_16_suimm5 = value;
      }
      break;
    case NDS32_OPERAND_SWID15 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 15, 32, total_length, pc, & fields->f_32t3_swid15);
      break;
    case NDS32_OPERAND_SWID5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 11, 5, 32, total_length, pc, & fields->f_16_swid5);
      break;
    case NDS32_OPERAND_SWID9 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 9, 32, total_length, pc, & fields->f_16_swid9);
      break;
    case NDS32_OPERAND_TLBOPST :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 5, 32, total_length, pc, & fields->f_32t4_ext5);
      break;
    case NDS32_OPERAND_UHI20 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 20, 32, total_length, pc, & fields->f_32t1_uhi20);
      break;
    case NDS32_OPERAND_UIMM12 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 12, 32, total_length, pc, & fields->f_32_12_12);
      break;
    case NDS32_OPERAND_UIMM19 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 7, 19, 32, total_length, pc, & fields->f_32_19_7);
      break;
    case NDS32_OPERAND_UIMM3 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 13, 3, 32, total_length, pc, & fields->f_16_uimm3);
      break;
    case NDS32_OPERAND_UIMM3_10 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 10, 3, 32, total_length, pc, & fields->f_16_uimm3_10);
      break;
    case NDS32_OPERAND_UIMM5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 5, 32, total_length, pc, & fields->f_32t3_uimm5);
      break;
    case NDS32_OPERAND_UIMM5D :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 11, 5, 32, total_length, pc, & value);
        value = ((value) << (3));
        fields->f_16_uimm5d = value;
      }
      break;
    case NDS32_OPERAND_UIMM5H :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 11, 5, 32, total_length, pc, & fields->f_16_uimm5);
      break;
    case NDS32_OPERAND_UIMM6W :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 10, 6, 32, total_length, pc, & value);
        value = ((value) << (2));
        fields->f_16_uimm6w = value;
      }
      break;
    case NDS32_OPERAND_UIMM8_S :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 8, 32, total_length, pc, & fields->f_32_uimm8_s);
      break;
    case NDS32_OPERAND_UIMM_SR10 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 10, 32, total_length, pc, & fields->f_32_sr10);
      break;
    case NDS32_OPERAND_ULO15 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 15, 32, total_length, pc, & fields->f_32t2_ulo15b);
      break;
    case NDS32_OPERAND_ULO15B :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 15, 32, total_length, pc, & fields->f_32t2_ulo15b);
      break;
    case NDS32_OPERAND_ULO15D :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 15, 32, total_length, pc, & value);
        value = ((value) << (3));
        fields->f_32t2_ulo15d = value;
      }
      break;
    case NDS32_OPERAND_ULO15H :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 15, 32, total_length, pc, & value);
        value = ((value) << (1));
        fields->f_32t2_ulo15h = value;
      }
      break;
    case NDS32_OPERAND_ULO15W :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 17, 15, 32, total_length, pc, & value);
        value = ((value) << (2));
        fields->f_32t2_ulo15w = value;
      }
      break;
    case NDS32_OPERAND_ULO3B :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 13, 3, 32, total_length, pc, & fields->f_16_ulo3b);
      break;
    case NDS32_OPERAND_ULO3H :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 13, 3, 32, total_length, pc, & value);
        value = ((value) << (1));
        fields->f_16_ulo3h = value;
      }
      break;
    case NDS32_OPERAND_ULO3W :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 13, 3, 32, total_length, pc, & value);
        value = ((value) << (2));
        fields->f_16_ulo3w = value;
      }
      break;
    case NDS32_OPERAND_ULO5 :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 22, 5, 32, total_length, pc, & fields->f_32t21_ulo5);
      break;
    case NDS32_OPERAND_ULO7W :
      {
        long value;
        length = extract_normal (cd, ex_info, insn_value, 0, 0, 9, 7, 32, total_length, pc, & value);
        value = ((value) << (2));
        fields->f_16_ulo7w = value;
      }
      break;
    case NDS32_OPERAND_USRIDX :
      length = extract_normal (cd, ex_info, insn_value, 0, 0, 12, 5, 32, total_length, pc, & fields->f_32_usr);
      break;

    default :
      /* xgettext:c-format */
      fprintf (stderr, _("Unrecognized field %d while decoding insn.\n"),
	       opindex);
      abort ();
    }

  return length;
}

cgen_insert_fn * const nds32_cgen_insert_handlers[] = 
{
  insert_insn_normal,
};

cgen_extract_fn * const nds32_cgen_extract_handlers[] = 
{
  extract_insn_normal,
};

int nds32_cgen_get_int_operand     (CGEN_CPU_DESC, int, const CGEN_FIELDS *);
bfd_vma nds32_cgen_get_vma_operand (CGEN_CPU_DESC, int, const CGEN_FIELDS *);

/* Getting values from cgen_fields is handled by a collection of functions.
   They are distinguished by the type of the VALUE argument they return.
   TODO: floating point, inlining support, remove cases where result type
   not appropriate.  */

int
nds32_cgen_get_int_operand (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
			     int opindex,
			     const CGEN_FIELDS * fields)
{
  int value;

  switch (opindex)
    {
    case NDS32_OPERAND_AR2IDX5_A :
      value = fields->f_32_aridx5_a;
      break;
    case NDS32_OPERAND_ARIDX4_A :
      value = fields->f_32_aridx4_a;
      break;
    case NDS32_OPERAND_ARIDX5_A :
      value = fields->f_32_aridx5_a;
      break;
    case NDS32_OPERAND_BITS :
      value = fields->f_16_uimm3;
      break;
    case NDS32_OPERAND_C1_15_A :
      value = fields->f_32_c1_15_a;
      break;
    case NDS32_OPERAND_CCTLLVL :
      value = fields->f_32tx_1_21;
      break;
    case NDS32_OPERAND_CCTLST :
      value = fields->f_32t4_ext5;
      break;
    case NDS32_OPERAND_CONCAT24 :
      value = fields->f_32_concat24;
      break;
    case NDS32_OPERAND_COPDR :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_COPWR :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_CPID :
      value = fields->f_32_2_26;
      break;
    case NDS32_OPERAND_CPID2 :
      value = fields->f_32tx_2_17;
      break;
    case NDS32_OPERAND_D1_A :
      value = fields->f_32_d1_a;
      break;
    case NDS32_OPERAND_DH2_16_A :
      value = fields->f_32_dh2_16_a;
      break;
    case NDS32_OPERAND_DH2_6_A :
      value = fields->f_32_dh2_6_a;
      break;
    case NDS32_OPERAND_DISP14 :
      value = fields->f_32t2_disp14;
      break;
    case NDS32_OPERAND_DISP16 :
      value = fields->f_32t1_disp16;
      break;
    case NDS32_OPERAND_DISP24 :
      value = fields->f_32t0_disp24;
      break;
    case NDS32_OPERAND_DISP8 :
      value = fields->f_32t1_disp8;
      break;
    case NDS32_OPERAND_DISP9 :
      value = fields->f_32t1_disp9;
      break;
    case NDS32_OPERAND_DPREFST :
      value = fields->f_32t2_st4;
      break;
    case NDS32_OPERAND_FDRA5 :
      value = fields->f_32_ra5;
      break;
    case NDS32_OPERAND_FDRB5 :
      value = fields->f_32_rb5;
      break;
    case NDS32_OPERAND_FDRT5 :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_FSRA5 :
      value = fields->f_32_ra5;
      break;
    case NDS32_OPERAND_FSRB5 :
      value = fields->f_32_rb5;
      break;
    case NDS32_OPERAND_FSRT5 :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_GROUPIDX :
      value = fields->f_32_group;
      break;
    case NDS32_OPERAND_HASH :
      value = 0;
      break;
    case NDS32_OPERAND_HSDISP8 :
      value = fields->f_16_hsdisp8;
      break;
    case NDS32_OPERAND_I2_1_A :
      value = fields->f_32_i2_1_a;
      break;
    case NDS32_OPERAND_IM1_4_A :
      value = fields->f_32_im1_4_a;
      break;
    case NDS32_OPERAND_IM5_I_A :
      value = fields->f_32_im5_i_a;
      break;
    case NDS32_OPERAND_IM5_M_A :
      value = fields->f_32_im5_m_a;
      break;
    case NDS32_OPERAND_IM6_I_0_A :
      value = fields->f_32_im6_i_0_a;
      break;
    case NDS32_OPERAND_IM6_I_1_A :
      value = fields->f_32_im6_i_1_a;
      break;
    case NDS32_OPERAND_IM6_M_0_A :
      value = fields->f_32_im6_m_0_a;
      break;
    case NDS32_OPERAND_IM6_M_1_A :
      value = fields->f_32_im6_m_1_a;
      break;
    case NDS32_OPERAND_IMM16_A :
      value = fields->f_32_imm16_a;
      break;
    case NDS32_OPERAND_IMM5U :
      value = fields->f_16_uimm5;
      break;
    case NDS32_OPERAND_LSBLOC_A :
      value = fields->f_32_lsbloc_a;
      break;
    case NDS32_OPERAND_M2_3_A :
      value = fields->f_32_m2_3_a;
      break;
    case NDS32_OPERAND_M2_5_A :
      value = fields->f_32_m2_5_a;
      break;
    case NDS32_OPERAND_MASK4 :
      value = fields->f_32t5_mask4;
      break;
    case NDS32_OPERAND_MFUSRIDX :
      value = fields->f_32_group_usr;
      break;
    case NDS32_OPERAND_MSYNCST :
      value = fields->f_32t3_ext3;
      break;
    case NDS32_OPERAND_MTUSRIDX :
      value = fields->f_32_group_usr;
      break;
    case NDS32_OPERAND_R10A5_A :
      value = fields->f_32_r10a5_a;
      break;
    case NDS32_OPERAND_R10A5_A_B :
      value = fields->f_32_r10a5_a;
      break;
    case NDS32_OPERAND_R10A5_A_T :
      value = fields->f_32_r10a5_a;
      break;
    case NDS32_OPERAND_R10B5_A :
      value = fields->f_32_r10b5_a;
      break;
    case NDS32_OPERAND_R10B5_A_B :
      value = fields->f_32_r10b5_a;
      break;
    case NDS32_OPERAND_R10B5_A_T :
      value = fields->f_32_r10b5_a;
      break;
    case NDS32_OPERAND_R10C5_0_A :
      value = fields->f_32_r10c5_0_a;
      break;
    case NDS32_OPERAND_R10C5_1_A :
      value = fields->f_32_r10c5_1_a;
      break;
    case NDS32_OPERAND_R10C5_A :
      value = fields->f_32_r10c5_a;
      break;
    case NDS32_OPERAND_RA3 :
      value = fields->f_16_ra3;
      break;
    case NDS32_OPERAND_RA4 :
      value = fields->f_16_ra4;
      break;
    case NDS32_OPERAND_RA4_19_A :
      value = fields->f_32_ra4_19_a;
      break;
    case NDS32_OPERAND_RA5 :
      value = fields->f_32_ra5;
      break;
    case NDS32_OPERAND_RA5_A :
      value = fields->f_32_ra5_a;
      break;
    case NDS32_OPERAND_RA5_A_B :
      value = fields->f_32_ra5_a;
      break;
    case NDS32_OPERAND_RA5_A_T :
      value = fields->f_32_ra5_a;
      break;
    case NDS32_OPERAND_RA5E :
      value = fields->f_16_ra5e;
      break;
    case NDS32_OPERAND_RA5H :
      value = fields->f_16_ra5h;
      break;
    case NDS32_OPERAND_RB3 :
      value = fields->f_16_rb3;
      break;
    case NDS32_OPERAND_RB3_14_A :
      value = fields->f_32_rb3_14_a;
      break;
    case NDS32_OPERAND_RB5 :
      value = fields->f_32_rb5;
      break;
    case NDS32_OPERAND_RB5_A :
      value = fields->f_32_rb5_a;
      break;
    case NDS32_OPERAND_RB5_A_B :
      value = fields->f_32_rb5_a;
      break;
    case NDS32_OPERAND_RB5_A_T :
      value = fields->f_32_rb5_a;
      break;
    case NDS32_OPERAND_RB5H :
      value = fields->f_16_rb5h;
      break;
    case NDS32_OPERAND_RB5P_A :
      value = fields->f_32_rb5p_a;
      break;
    case NDS32_OPERAND_RB5P_A_B :
      value = fields->f_32_rb5p_a;
      break;
    case NDS32_OPERAND_RB5P_A_T :
      value = fields->f_32_rb5p_a;
      break;
    case NDS32_OPERAND_RC1_5_A :
      value = fields->f_32_rc1_5_a;
      break;
    case NDS32_OPERAND_RC2_11_A :
      value = fields->f_32_rc2_11_a;
      break;
    case NDS32_OPERAND_RC4_A :
      value = fields->f_32_rc4_a;
      break;
    case NDS32_OPERAND_RC5_0_A :
      value = fields->f_32_rc5_0_a;
      break;
    case NDS32_OPERAND_RC5_1_A :
      value = fields->f_32_rc5_1_a;
      break;
    case NDS32_OPERAND_RD1 :
      value = fields->f_32_rd1;
      break;
    case NDS32_OPERAND_RD1HL :
      value = fields->f_32_rd1hl;
      break;
    case NDS32_OPERAND_RD5_A :
      value = fields->f_32_rd5_a;
      break;
    case NDS32_OPERAND_REGLIST :
      value = fields->f_16_mask2;
      break;
    case NDS32_OPERAND_RS5 :
      value = fields->f_32_rs5;
      break;
    case NDS32_OPERAND_RT3 :
      value = fields->f_16_rt3;
      break;
    case NDS32_OPERAND_RT3_7 :
      value = fields->f_16_rt3_7;
      break;
    case NDS32_OPERAND_RT3E5 :
      value = fields->f_16_rt3;
      break;
    case NDS32_OPERAND_RT4 :
      value = fields->f_16_rt4;
      break;
    case NDS32_OPERAND_RT5 :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_RT5E :
      value = fields->f_16_rt5e;
      break;
    case NDS32_OPERAND_RT5H :
      value = fields->f_16_rt5h;
      break;
    case NDS32_OPERAND_RTH5 :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_RTL5 :
      value = fields->f_32_ra5;
      break;
    case NDS32_OPERAND_SI :
      value = fields->f_32t3_sub10si;
      break;
    case NDS32_OPERAND_SIMM10 :
      value = fields->f_16_simm10;
      break;
    case NDS32_OPERAND_SIMM11 :
      value = fields->f_32t2_simm11;
      break;
    case NDS32_OPERAND_SIMM5H :
      value = fields->f_16_simm5;
      break;
    case NDS32_OPERAND_SIMM5W :
      value = fields->f_16_simm5w;
      break;
    case NDS32_OPERAND_SLO12D :
      value = fields->f_32tx_slo12d;
      break;
    case NDS32_OPERAND_SLO12W :
      value = fields->f_32tx_slo12w;
      break;
    case NDS32_OPERAND_SLO15 :
      value = fields->f_32t2_slo15b;
      break;
    case NDS32_OPERAND_SLO15B :
      value = fields->f_32t2_slo15b;
      break;
    case NDS32_OPERAND_SLO15D :
      value = fields->f_32t2_slo15d;
      break;
    case NDS32_OPERAND_SLO15H :
      value = fields->f_32t2_slo15h;
      break;
    case NDS32_OPERAND_SLO15W :
      value = fields->f_32t2_slo15w;
      break;
    case NDS32_OPERAND_SLO17W :
      value = fields->f_32_slo17w;
      break;
    case NDS32_OPERAND_SLO18H :
      value = fields->f_32_slo18h;
      break;
    case NDS32_OPERAND_SLO19 :
      value = fields->f_32_slo19;
      break;
    case NDS32_OPERAND_SLO20 :
      value = fields->f_32t1_slo20;
      break;
    case NDS32_OPERAND_SR10 :
      value = fields->f_32_sr10;
      break;
    case NDS32_OPERAND_STANDBYST :
      value = fields->f_32t4_ext2;
      break;
    case NDS32_OPERAND_SUIMM5 :
      value = fields->f_16_suimm5;
      break;
    case NDS32_OPERAND_SWID15 :
      value = fields->f_32t3_swid15;
      break;
    case NDS32_OPERAND_SWID5 :
      value = fields->f_16_swid5;
      break;
    case NDS32_OPERAND_SWID9 :
      value = fields->f_16_swid9;
      break;
    case NDS32_OPERAND_TLBOPST :
      value = fields->f_32t4_ext5;
      break;
    case NDS32_OPERAND_UHI20 :
      value = fields->f_32t1_uhi20;
      break;
    case NDS32_OPERAND_UIMM12 :
      value = fields->f_32_12_12;
      break;
    case NDS32_OPERAND_UIMM19 :
      value = fields->f_32_19_7;
      break;
    case NDS32_OPERAND_UIMM3 :
      value = fields->f_16_uimm3;
      break;
    case NDS32_OPERAND_UIMM3_10 :
      value = fields->f_16_uimm3_10;
      break;
    case NDS32_OPERAND_UIMM5 :
      value = fields->f_32t3_uimm5;
      break;
    case NDS32_OPERAND_UIMM5D :
      value = fields->f_16_uimm5d;
      break;
    case NDS32_OPERAND_UIMM5H :
      value = fields->f_16_uimm5;
      break;
    case NDS32_OPERAND_UIMM6W :
      value = fields->f_16_uimm6w;
      break;
    case NDS32_OPERAND_UIMM8_S :
      value = fields->f_32_uimm8_s;
      break;
    case NDS32_OPERAND_UIMM_SR10 :
      value = fields->f_32_sr10;
      break;
    case NDS32_OPERAND_ULO15 :
      value = fields->f_32t2_ulo15b;
      break;
    case NDS32_OPERAND_ULO15B :
      value = fields->f_32t2_ulo15b;
      break;
    case NDS32_OPERAND_ULO15D :
      value = fields->f_32t2_ulo15d;
      break;
    case NDS32_OPERAND_ULO15H :
      value = fields->f_32t2_ulo15h;
      break;
    case NDS32_OPERAND_ULO15W :
      value = fields->f_32t2_ulo15w;
      break;
    case NDS32_OPERAND_ULO3B :
      value = fields->f_16_ulo3b;
      break;
    case NDS32_OPERAND_ULO3H :
      value = fields->f_16_ulo3h;
      break;
    case NDS32_OPERAND_ULO3W :
      value = fields->f_16_ulo3w;
      break;
    case NDS32_OPERAND_ULO5 :
      value = fields->f_32t21_ulo5;
      break;
    case NDS32_OPERAND_ULO7W :
      value = fields->f_16_ulo7w;
      break;
    case NDS32_OPERAND_USRIDX :
      value = fields->f_32_usr;
      break;

    default :
      /* xgettext:c-format */
      fprintf (stderr, _("Unrecognized field %d while getting int operand.\n"),
		       opindex);
      abort ();
  }

  return value;
}

bfd_vma
nds32_cgen_get_vma_operand (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
			     int opindex,
			     const CGEN_FIELDS * fields)
{
  bfd_vma value;

  switch (opindex)
    {
    case NDS32_OPERAND_AR2IDX5_A :
      value = fields->f_32_aridx5_a;
      break;
    case NDS32_OPERAND_ARIDX4_A :
      value = fields->f_32_aridx4_a;
      break;
    case NDS32_OPERAND_ARIDX5_A :
      value = fields->f_32_aridx5_a;
      break;
    case NDS32_OPERAND_BITS :
      value = fields->f_16_uimm3;
      break;
    case NDS32_OPERAND_C1_15_A :
      value = fields->f_32_c1_15_a;
      break;
    case NDS32_OPERAND_CCTLLVL :
      value = fields->f_32tx_1_21;
      break;
    case NDS32_OPERAND_CCTLST :
      value = fields->f_32t4_ext5;
      break;
    case NDS32_OPERAND_CONCAT24 :
      value = fields->f_32_concat24;
      break;
    case NDS32_OPERAND_COPDR :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_COPWR :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_CPID :
      value = fields->f_32_2_26;
      break;
    case NDS32_OPERAND_CPID2 :
      value = fields->f_32tx_2_17;
      break;
    case NDS32_OPERAND_D1_A :
      value = fields->f_32_d1_a;
      break;
    case NDS32_OPERAND_DH2_16_A :
      value = fields->f_32_dh2_16_a;
      break;
    case NDS32_OPERAND_DH2_6_A :
      value = fields->f_32_dh2_6_a;
      break;
    case NDS32_OPERAND_DISP14 :
      value = fields->f_32t2_disp14;
      break;
    case NDS32_OPERAND_DISP16 :
      value = fields->f_32t1_disp16;
      break;
    case NDS32_OPERAND_DISP24 :
      value = fields->f_32t0_disp24;
      break;
    case NDS32_OPERAND_DISP8 :
      value = fields->f_32t1_disp8;
      break;
    case NDS32_OPERAND_DISP9 :
      value = fields->f_32t1_disp9;
      break;
    case NDS32_OPERAND_DPREFST :
      value = fields->f_32t2_st4;
      break;
    case NDS32_OPERAND_FDRA5 :
      value = fields->f_32_ra5;
      break;
    case NDS32_OPERAND_FDRB5 :
      value = fields->f_32_rb5;
      break;
    case NDS32_OPERAND_FDRT5 :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_FSRA5 :
      value = fields->f_32_ra5;
      break;
    case NDS32_OPERAND_FSRB5 :
      value = fields->f_32_rb5;
      break;
    case NDS32_OPERAND_FSRT5 :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_GROUPIDX :
      value = fields->f_32_group;
      break;
    case NDS32_OPERAND_HASH :
      value = 0;
      break;
    case NDS32_OPERAND_HSDISP8 :
      value = fields->f_16_hsdisp8;
      break;
    case NDS32_OPERAND_I2_1_A :
      value = fields->f_32_i2_1_a;
      break;
    case NDS32_OPERAND_IM1_4_A :
      value = fields->f_32_im1_4_a;
      break;
    case NDS32_OPERAND_IM5_I_A :
      value = fields->f_32_im5_i_a;
      break;
    case NDS32_OPERAND_IM5_M_A :
      value = fields->f_32_im5_m_a;
      break;
    case NDS32_OPERAND_IM6_I_0_A :
      value = fields->f_32_im6_i_0_a;
      break;
    case NDS32_OPERAND_IM6_I_1_A :
      value = fields->f_32_im6_i_1_a;
      break;
    case NDS32_OPERAND_IM6_M_0_A :
      value = fields->f_32_im6_m_0_a;
      break;
    case NDS32_OPERAND_IM6_M_1_A :
      value = fields->f_32_im6_m_1_a;
      break;
    case NDS32_OPERAND_IMM16_A :
      value = fields->f_32_imm16_a;
      break;
    case NDS32_OPERAND_IMM5U :
      value = fields->f_16_uimm5;
      break;
    case NDS32_OPERAND_LSBLOC_A :
      value = fields->f_32_lsbloc_a;
      break;
    case NDS32_OPERAND_M2_3_A :
      value = fields->f_32_m2_3_a;
      break;
    case NDS32_OPERAND_M2_5_A :
      value = fields->f_32_m2_5_a;
      break;
    case NDS32_OPERAND_MASK4 :
      value = fields->f_32t5_mask4;
      break;
    case NDS32_OPERAND_MFUSRIDX :
      value = fields->f_32_group_usr;
      break;
    case NDS32_OPERAND_MSYNCST :
      value = fields->f_32t3_ext3;
      break;
    case NDS32_OPERAND_MTUSRIDX :
      value = fields->f_32_group_usr;
      break;
    case NDS32_OPERAND_R10A5_A :
      value = fields->f_32_r10a5_a;
      break;
    case NDS32_OPERAND_R10A5_A_B :
      value = fields->f_32_r10a5_a;
      break;
    case NDS32_OPERAND_R10A5_A_T :
      value = fields->f_32_r10a5_a;
      break;
    case NDS32_OPERAND_R10B5_A :
      value = fields->f_32_r10b5_a;
      break;
    case NDS32_OPERAND_R10B5_A_B :
      value = fields->f_32_r10b5_a;
      break;
    case NDS32_OPERAND_R10B5_A_T :
      value = fields->f_32_r10b5_a;
      break;
    case NDS32_OPERAND_R10C5_0_A :
      value = fields->f_32_r10c5_0_a;
      break;
    case NDS32_OPERAND_R10C5_1_A :
      value = fields->f_32_r10c5_1_a;
      break;
    case NDS32_OPERAND_R10C5_A :
      value = fields->f_32_r10c5_a;
      break;
    case NDS32_OPERAND_RA3 :
      value = fields->f_16_ra3;
      break;
    case NDS32_OPERAND_RA4 :
      value = fields->f_16_ra4;
      break;
    case NDS32_OPERAND_RA4_19_A :
      value = fields->f_32_ra4_19_a;
      break;
    case NDS32_OPERAND_RA5 :
      value = fields->f_32_ra5;
      break;
    case NDS32_OPERAND_RA5_A :
      value = fields->f_32_ra5_a;
      break;
    case NDS32_OPERAND_RA5_A_B :
      value = fields->f_32_ra5_a;
      break;
    case NDS32_OPERAND_RA5_A_T :
      value = fields->f_32_ra5_a;
      break;
    case NDS32_OPERAND_RA5E :
      value = fields->f_16_ra5e;
      break;
    case NDS32_OPERAND_RA5H :
      value = fields->f_16_ra5h;
      break;
    case NDS32_OPERAND_RB3 :
      value = fields->f_16_rb3;
      break;
    case NDS32_OPERAND_RB3_14_A :
      value = fields->f_32_rb3_14_a;
      break;
    case NDS32_OPERAND_RB5 :
      value = fields->f_32_rb5;
      break;
    case NDS32_OPERAND_RB5_A :
      value = fields->f_32_rb5_a;
      break;
    case NDS32_OPERAND_RB5_A_B :
      value = fields->f_32_rb5_a;
      break;
    case NDS32_OPERAND_RB5_A_T :
      value = fields->f_32_rb5_a;
      break;
    case NDS32_OPERAND_RB5H :
      value = fields->f_16_rb5h;
      break;
    case NDS32_OPERAND_RB5P_A :
      value = fields->f_32_rb5p_a;
      break;
    case NDS32_OPERAND_RB5P_A_B :
      value = fields->f_32_rb5p_a;
      break;
    case NDS32_OPERAND_RB5P_A_T :
      value = fields->f_32_rb5p_a;
      break;
    case NDS32_OPERAND_RC1_5_A :
      value = fields->f_32_rc1_5_a;
      break;
    case NDS32_OPERAND_RC2_11_A :
      value = fields->f_32_rc2_11_a;
      break;
    case NDS32_OPERAND_RC4_A :
      value = fields->f_32_rc4_a;
      break;
    case NDS32_OPERAND_RC5_0_A :
      value = fields->f_32_rc5_0_a;
      break;
    case NDS32_OPERAND_RC5_1_A :
      value = fields->f_32_rc5_1_a;
      break;
    case NDS32_OPERAND_RD1 :
      value = fields->f_32_rd1;
      break;
    case NDS32_OPERAND_RD1HL :
      value = fields->f_32_rd1hl;
      break;
    case NDS32_OPERAND_RD5_A :
      value = fields->f_32_rd5_a;
      break;
    case NDS32_OPERAND_REGLIST :
      value = fields->f_16_mask2;
      break;
    case NDS32_OPERAND_RS5 :
      value = fields->f_32_rs5;
      break;
    case NDS32_OPERAND_RT3 :
      value = fields->f_16_rt3;
      break;
    case NDS32_OPERAND_RT3_7 :
      value = fields->f_16_rt3_7;
      break;
    case NDS32_OPERAND_RT3E5 :
      value = fields->f_16_rt3;
      break;
    case NDS32_OPERAND_RT4 :
      value = fields->f_16_rt4;
      break;
    case NDS32_OPERAND_RT5 :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_RT5E :
      value = fields->f_16_rt5e;
      break;
    case NDS32_OPERAND_RT5H :
      value = fields->f_16_rt5h;
      break;
    case NDS32_OPERAND_RTH5 :
      value = fields->f_32_rt5;
      break;
    case NDS32_OPERAND_RTL5 :
      value = fields->f_32_ra5;
      break;
    case NDS32_OPERAND_SI :
      value = fields->f_32t3_sub10si;
      break;
    case NDS32_OPERAND_SIMM10 :
      value = fields->f_16_simm10;
      break;
    case NDS32_OPERAND_SIMM11 :
      value = fields->f_32t2_simm11;
      break;
    case NDS32_OPERAND_SIMM5H :
      value = fields->f_16_simm5;
      break;
    case NDS32_OPERAND_SIMM5W :
      value = fields->f_16_simm5w;
      break;
    case NDS32_OPERAND_SLO12D :
      value = fields->f_32tx_slo12d;
      break;
    case NDS32_OPERAND_SLO12W :
      value = fields->f_32tx_slo12w;
      break;
    case NDS32_OPERAND_SLO15 :
      value = fields->f_32t2_slo15b;
      break;
    case NDS32_OPERAND_SLO15B :
      value = fields->f_32t2_slo15b;
      break;
    case NDS32_OPERAND_SLO15D :
      value = fields->f_32t2_slo15d;
      break;
    case NDS32_OPERAND_SLO15H :
      value = fields->f_32t2_slo15h;
      break;
    case NDS32_OPERAND_SLO15W :
      value = fields->f_32t2_slo15w;
      break;
    case NDS32_OPERAND_SLO17W :
      value = fields->f_32_slo17w;
      break;
    case NDS32_OPERAND_SLO18H :
      value = fields->f_32_slo18h;
      break;
    case NDS32_OPERAND_SLO19 :
      value = fields->f_32_slo19;
      break;
    case NDS32_OPERAND_SLO20 :
      value = fields->f_32t1_slo20;
      break;
    case NDS32_OPERAND_SR10 :
      value = fields->f_32_sr10;
      break;
    case NDS32_OPERAND_STANDBYST :
      value = fields->f_32t4_ext2;
      break;
    case NDS32_OPERAND_SUIMM5 :
      value = fields->f_16_suimm5;
      break;
    case NDS32_OPERAND_SWID15 :
      value = fields->f_32t3_swid15;
      break;
    case NDS32_OPERAND_SWID5 :
      value = fields->f_16_swid5;
      break;
    case NDS32_OPERAND_SWID9 :
      value = fields->f_16_swid9;
      break;
    case NDS32_OPERAND_TLBOPST :
      value = fields->f_32t4_ext5;
      break;
    case NDS32_OPERAND_UHI20 :
      value = fields->f_32t1_uhi20;
      break;
    case NDS32_OPERAND_UIMM12 :
      value = fields->f_32_12_12;
      break;
    case NDS32_OPERAND_UIMM19 :
      value = fields->f_32_19_7;
      break;
    case NDS32_OPERAND_UIMM3 :
      value = fields->f_16_uimm3;
      break;
    case NDS32_OPERAND_UIMM3_10 :
      value = fields->f_16_uimm3_10;
      break;
    case NDS32_OPERAND_UIMM5 :
      value = fields->f_32t3_uimm5;
      break;
    case NDS32_OPERAND_UIMM5D :
      value = fields->f_16_uimm5d;
      break;
    case NDS32_OPERAND_UIMM5H :
      value = fields->f_16_uimm5;
      break;
    case NDS32_OPERAND_UIMM6W :
      value = fields->f_16_uimm6w;
      break;
    case NDS32_OPERAND_UIMM8_S :
      value = fields->f_32_uimm8_s;
      break;
    case NDS32_OPERAND_UIMM_SR10 :
      value = fields->f_32_sr10;
      break;
    case NDS32_OPERAND_ULO15 :
      value = fields->f_32t2_ulo15b;
      break;
    case NDS32_OPERAND_ULO15B :
      value = fields->f_32t2_ulo15b;
      break;
    case NDS32_OPERAND_ULO15D :
      value = fields->f_32t2_ulo15d;
      break;
    case NDS32_OPERAND_ULO15H :
      value = fields->f_32t2_ulo15h;
      break;
    case NDS32_OPERAND_ULO15W :
      value = fields->f_32t2_ulo15w;
      break;
    case NDS32_OPERAND_ULO3B :
      value = fields->f_16_ulo3b;
      break;
    case NDS32_OPERAND_ULO3H :
      value = fields->f_16_ulo3h;
      break;
    case NDS32_OPERAND_ULO3W :
      value = fields->f_16_ulo3w;
      break;
    case NDS32_OPERAND_ULO5 :
      value = fields->f_32t21_ulo5;
      break;
    case NDS32_OPERAND_ULO7W :
      value = fields->f_16_ulo7w;
      break;
    case NDS32_OPERAND_USRIDX :
      value = fields->f_32_usr;
      break;

    default :
      /* xgettext:c-format */
      fprintf (stderr, _("Unrecognized field %d while getting vma operand.\n"),
		       opindex);
      abort ();
  }

  return value;
}

void nds32_cgen_set_int_operand  (CGEN_CPU_DESC, int, CGEN_FIELDS *, int);
void nds32_cgen_set_vma_operand  (CGEN_CPU_DESC, int, CGEN_FIELDS *, bfd_vma);

/* Stuffing values in cgen_fields is handled by a collection of functions.
   They are distinguished by the type of the VALUE argument they accept.
   TODO: floating point, inlining support, remove cases where argument type
   not appropriate.  */

void
nds32_cgen_set_int_operand (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
			     int opindex,
			     CGEN_FIELDS * fields,
			     int value)
{
  switch (opindex)
    {
    case NDS32_OPERAND_AR2IDX5_A :
      fields->f_32_aridx5_a = value;
      break;
    case NDS32_OPERAND_ARIDX4_A :
      fields->f_32_aridx4_a = value;
      break;
    case NDS32_OPERAND_ARIDX5_A :
      fields->f_32_aridx5_a = value;
      break;
    case NDS32_OPERAND_BITS :
      fields->f_16_uimm3 = value;
      break;
    case NDS32_OPERAND_C1_15_A :
      fields->f_32_c1_15_a = value;
      break;
    case NDS32_OPERAND_CCTLLVL :
      fields->f_32tx_1_21 = value;
      break;
    case NDS32_OPERAND_CCTLST :
      fields->f_32t4_ext5 = value;
      break;
    case NDS32_OPERAND_CONCAT24 :
      fields->f_32_concat24 = value;
      break;
    case NDS32_OPERAND_COPDR :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_COPWR :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_CPID :
      fields->f_32_2_26 = value;
      break;
    case NDS32_OPERAND_CPID2 :
      fields->f_32tx_2_17 = value;
      break;
    case NDS32_OPERAND_D1_A :
      fields->f_32_d1_a = value;
      break;
    case NDS32_OPERAND_DH2_16_A :
      fields->f_32_dh2_16_a = value;
      break;
    case NDS32_OPERAND_DH2_6_A :
      fields->f_32_dh2_6_a = value;
      break;
    case NDS32_OPERAND_DISP14 :
      fields->f_32t2_disp14 = value;
      break;
    case NDS32_OPERAND_DISP16 :
      fields->f_32t1_disp16 = value;
      break;
    case NDS32_OPERAND_DISP24 :
      fields->f_32t0_disp24 = value;
      break;
    case NDS32_OPERAND_DISP8 :
      fields->f_32t1_disp8 = value;
      break;
    case NDS32_OPERAND_DISP9 :
      fields->f_32t1_disp9 = value;
      break;
    case NDS32_OPERAND_DPREFST :
      fields->f_32t2_st4 = value;
      break;
    case NDS32_OPERAND_FDRA5 :
      fields->f_32_ra5 = value;
      break;
    case NDS32_OPERAND_FDRB5 :
      fields->f_32_rb5 = value;
      break;
    case NDS32_OPERAND_FDRT5 :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_FSRA5 :
      fields->f_32_ra5 = value;
      break;
    case NDS32_OPERAND_FSRB5 :
      fields->f_32_rb5 = value;
      break;
    case NDS32_OPERAND_FSRT5 :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_GROUPIDX :
      fields->f_32_group = value;
      break;
    case NDS32_OPERAND_HASH :
      break;
    case NDS32_OPERAND_HSDISP8 :
      fields->f_16_hsdisp8 = value;
      break;
    case NDS32_OPERAND_I2_1_A :
      fields->f_32_i2_1_a = value;
      break;
    case NDS32_OPERAND_IM1_4_A :
      fields->f_32_im1_4_a = value;
      break;
    case NDS32_OPERAND_IM5_I_A :
      fields->f_32_im5_i_a = value;
      break;
    case NDS32_OPERAND_IM5_M_A :
      fields->f_32_im5_m_a = value;
      break;
    case NDS32_OPERAND_IM6_I_0_A :
      fields->f_32_im6_i_0_a = value;
      break;
    case NDS32_OPERAND_IM6_I_1_A :
      fields->f_32_im6_i_1_a = value;
      break;
    case NDS32_OPERAND_IM6_M_0_A :
      fields->f_32_im6_m_0_a = value;
      break;
    case NDS32_OPERAND_IM6_M_1_A :
      fields->f_32_im6_m_1_a = value;
      break;
    case NDS32_OPERAND_IMM16_A :
      fields->f_32_imm16_a = value;
      break;
    case NDS32_OPERAND_IMM5U :
      fields->f_16_uimm5 = value;
      break;
    case NDS32_OPERAND_LSBLOC_A :
      fields->f_32_lsbloc_a = value;
      break;
    case NDS32_OPERAND_M2_3_A :
      fields->f_32_m2_3_a = value;
      break;
    case NDS32_OPERAND_M2_5_A :
      fields->f_32_m2_5_a = value;
      break;
    case NDS32_OPERAND_MASK4 :
      fields->f_32t5_mask4 = value;
      break;
    case NDS32_OPERAND_MFUSRIDX :
      fields->f_32_group_usr = value;
      break;
    case NDS32_OPERAND_MSYNCST :
      fields->f_32t3_ext3 = value;
      break;
    case NDS32_OPERAND_MTUSRIDX :
      fields->f_32_group_usr = value;
      break;
    case NDS32_OPERAND_R10A5_A :
      fields->f_32_r10a5_a = value;
      break;
    case NDS32_OPERAND_R10A5_A_B :
      fields->f_32_r10a5_a = value;
      break;
    case NDS32_OPERAND_R10A5_A_T :
      fields->f_32_r10a5_a = value;
      break;
    case NDS32_OPERAND_R10B5_A :
      fields->f_32_r10b5_a = value;
      break;
    case NDS32_OPERAND_R10B5_A_B :
      fields->f_32_r10b5_a = value;
      break;
    case NDS32_OPERAND_R10B5_A_T :
      fields->f_32_r10b5_a = value;
      break;
    case NDS32_OPERAND_R10C5_0_A :
      fields->f_32_r10c5_0_a = value;
      break;
    case NDS32_OPERAND_R10C5_1_A :
      fields->f_32_r10c5_1_a = value;
      break;
    case NDS32_OPERAND_R10C5_A :
      fields->f_32_r10c5_a = value;
      break;
    case NDS32_OPERAND_RA3 :
      fields->f_16_ra3 = value;
      break;
    case NDS32_OPERAND_RA4 :
      fields->f_16_ra4 = value;
      break;
    case NDS32_OPERAND_RA4_19_A :
      fields->f_32_ra4_19_a = value;
      break;
    case NDS32_OPERAND_RA5 :
      fields->f_32_ra5 = value;
      break;
    case NDS32_OPERAND_RA5_A :
      fields->f_32_ra5_a = value;
      break;
    case NDS32_OPERAND_RA5_A_B :
      fields->f_32_ra5_a = value;
      break;
    case NDS32_OPERAND_RA5_A_T :
      fields->f_32_ra5_a = value;
      break;
    case NDS32_OPERAND_RA5E :
      fields->f_16_ra5e = value;
      break;
    case NDS32_OPERAND_RA5H :
      fields->f_16_ra5h = value;
      break;
    case NDS32_OPERAND_RB3 :
      fields->f_16_rb3 = value;
      break;
    case NDS32_OPERAND_RB3_14_A :
      fields->f_32_rb3_14_a = value;
      break;
    case NDS32_OPERAND_RB5 :
      fields->f_32_rb5 = value;
      break;
    case NDS32_OPERAND_RB5_A :
      fields->f_32_rb5_a = value;
      break;
    case NDS32_OPERAND_RB5_A_B :
      fields->f_32_rb5_a = value;
      break;
    case NDS32_OPERAND_RB5_A_T :
      fields->f_32_rb5_a = value;
      break;
    case NDS32_OPERAND_RB5H :
      fields->f_16_rb5h = value;
      break;
    case NDS32_OPERAND_RB5P_A :
      fields->f_32_rb5p_a = value;
      break;
    case NDS32_OPERAND_RB5P_A_B :
      fields->f_32_rb5p_a = value;
      break;
    case NDS32_OPERAND_RB5P_A_T :
      fields->f_32_rb5p_a = value;
      break;
    case NDS32_OPERAND_RC1_5_A :
      fields->f_32_rc1_5_a = value;
      break;
    case NDS32_OPERAND_RC2_11_A :
      fields->f_32_rc2_11_a = value;
      break;
    case NDS32_OPERAND_RC4_A :
      fields->f_32_rc4_a = value;
      break;
    case NDS32_OPERAND_RC5_0_A :
      fields->f_32_rc5_0_a = value;
      break;
    case NDS32_OPERAND_RC5_1_A :
      fields->f_32_rc5_1_a = value;
      break;
    case NDS32_OPERAND_RD1 :
      fields->f_32_rd1 = value;
      break;
    case NDS32_OPERAND_RD1HL :
      fields->f_32_rd1hl = value;
      break;
    case NDS32_OPERAND_RD5_A :
      fields->f_32_rd5_a = value;
      break;
    case NDS32_OPERAND_REGLIST :
      fields->f_16_mask2 = value;
      break;
    case NDS32_OPERAND_RS5 :
      fields->f_32_rs5 = value;
      break;
    case NDS32_OPERAND_RT3 :
      fields->f_16_rt3 = value;
      break;
    case NDS32_OPERAND_RT3_7 :
      fields->f_16_rt3_7 = value;
      break;
    case NDS32_OPERAND_RT3E5 :
      fields->f_16_rt3 = value;
      break;
    case NDS32_OPERAND_RT4 :
      fields->f_16_rt4 = value;
      break;
    case NDS32_OPERAND_RT5 :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_RT5E :
      fields->f_16_rt5e = value;
      break;
    case NDS32_OPERAND_RT5H :
      fields->f_16_rt5h = value;
      break;
    case NDS32_OPERAND_RTH5 :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_RTL5 :
      fields->f_32_ra5 = value;
      break;
    case NDS32_OPERAND_SI :
      fields->f_32t3_sub10si = value;
      break;
    case NDS32_OPERAND_SIMM10 :
      fields->f_16_simm10 = value;
      break;
    case NDS32_OPERAND_SIMM11 :
      fields->f_32t2_simm11 = value;
      break;
    case NDS32_OPERAND_SIMM5H :
      fields->f_16_simm5 = value;
      break;
    case NDS32_OPERAND_SIMM5W :
      fields->f_16_simm5w = value;
      break;
    case NDS32_OPERAND_SLO12D :
      fields->f_32tx_slo12d = value;
      break;
    case NDS32_OPERAND_SLO12W :
      fields->f_32tx_slo12w = value;
      break;
    case NDS32_OPERAND_SLO15 :
      fields->f_32t2_slo15b = value;
      break;
    case NDS32_OPERAND_SLO15B :
      fields->f_32t2_slo15b = value;
      break;
    case NDS32_OPERAND_SLO15D :
      fields->f_32t2_slo15d = value;
      break;
    case NDS32_OPERAND_SLO15H :
      fields->f_32t2_slo15h = value;
      break;
    case NDS32_OPERAND_SLO15W :
      fields->f_32t2_slo15w = value;
      break;
    case NDS32_OPERAND_SLO17W :
      fields->f_32_slo17w = value;
      break;
    case NDS32_OPERAND_SLO18H :
      fields->f_32_slo18h = value;
      break;
    case NDS32_OPERAND_SLO19 :
      fields->f_32_slo19 = value;
      break;
    case NDS32_OPERAND_SLO20 :
      fields->f_32t1_slo20 = value;
      break;
    case NDS32_OPERAND_SR10 :
      fields->f_32_sr10 = value;
      break;
    case NDS32_OPERAND_STANDBYST :
      fields->f_32t4_ext2 = value;
      break;
    case NDS32_OPERAND_SUIMM5 :
      fields->f_16_suimm5 = value;
      break;
    case NDS32_OPERAND_SWID15 :
      fields->f_32t3_swid15 = value;
      break;
    case NDS32_OPERAND_SWID5 :
      fields->f_16_swid5 = value;
      break;
    case NDS32_OPERAND_SWID9 :
      fields->f_16_swid9 = value;
      break;
    case NDS32_OPERAND_TLBOPST :
      fields->f_32t4_ext5 = value;
      break;
    case NDS32_OPERAND_UHI20 :
      fields->f_32t1_uhi20 = value;
      break;
    case NDS32_OPERAND_UIMM12 :
      fields->f_32_12_12 = value;
      break;
    case NDS32_OPERAND_UIMM19 :
      fields->f_32_19_7 = value;
      break;
    case NDS32_OPERAND_UIMM3 :
      fields->f_16_uimm3 = value;
      break;
    case NDS32_OPERAND_UIMM3_10 :
      fields->f_16_uimm3_10 = value;
      break;
    case NDS32_OPERAND_UIMM5 :
      fields->f_32t3_uimm5 = value;
      break;
    case NDS32_OPERAND_UIMM5D :
      fields->f_16_uimm5d = value;
      break;
    case NDS32_OPERAND_UIMM5H :
      fields->f_16_uimm5 = value;
      break;
    case NDS32_OPERAND_UIMM6W :
      fields->f_16_uimm6w = value;
      break;
    case NDS32_OPERAND_UIMM8_S :
      fields->f_32_uimm8_s = value;
      break;
    case NDS32_OPERAND_UIMM_SR10 :
      fields->f_32_sr10 = value;
      break;
    case NDS32_OPERAND_ULO15 :
      fields->f_32t2_ulo15b = value;
      break;
    case NDS32_OPERAND_ULO15B :
      fields->f_32t2_ulo15b = value;
      break;
    case NDS32_OPERAND_ULO15D :
      fields->f_32t2_ulo15d = value;
      break;
    case NDS32_OPERAND_ULO15H :
      fields->f_32t2_ulo15h = value;
      break;
    case NDS32_OPERAND_ULO15W :
      fields->f_32t2_ulo15w = value;
      break;
    case NDS32_OPERAND_ULO3B :
      fields->f_16_ulo3b = value;
      break;
    case NDS32_OPERAND_ULO3H :
      fields->f_16_ulo3h = value;
      break;
    case NDS32_OPERAND_ULO3W :
      fields->f_16_ulo3w = value;
      break;
    case NDS32_OPERAND_ULO5 :
      fields->f_32t21_ulo5 = value;
      break;
    case NDS32_OPERAND_ULO7W :
      fields->f_16_ulo7w = value;
      break;
    case NDS32_OPERAND_USRIDX :
      fields->f_32_usr = value;
      break;

    default :
      /* xgettext:c-format */
      fprintf (stderr, _("Unrecognized field %d while setting int operand.\n"),
		       opindex);
      abort ();
  }
}

void
nds32_cgen_set_vma_operand (CGEN_CPU_DESC cd ATTRIBUTE_UNUSED,
			     int opindex,
			     CGEN_FIELDS * fields,
			     bfd_vma value)
{
  switch (opindex)
    {
    case NDS32_OPERAND_AR2IDX5_A :
      fields->f_32_aridx5_a = value;
      break;
    case NDS32_OPERAND_ARIDX4_A :
      fields->f_32_aridx4_a = value;
      break;
    case NDS32_OPERAND_ARIDX5_A :
      fields->f_32_aridx5_a = value;
      break;
    case NDS32_OPERAND_BITS :
      fields->f_16_uimm3 = value;
      break;
    case NDS32_OPERAND_C1_15_A :
      fields->f_32_c1_15_a = value;
      break;
    case NDS32_OPERAND_CCTLLVL :
      fields->f_32tx_1_21 = value;
      break;
    case NDS32_OPERAND_CCTLST :
      fields->f_32t4_ext5 = value;
      break;
    case NDS32_OPERAND_CONCAT24 :
      fields->f_32_concat24 = value;
      break;
    case NDS32_OPERAND_COPDR :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_COPWR :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_CPID :
      fields->f_32_2_26 = value;
      break;
    case NDS32_OPERAND_CPID2 :
      fields->f_32tx_2_17 = value;
      break;
    case NDS32_OPERAND_D1_A :
      fields->f_32_d1_a = value;
      break;
    case NDS32_OPERAND_DH2_16_A :
      fields->f_32_dh2_16_a = value;
      break;
    case NDS32_OPERAND_DH2_6_A :
      fields->f_32_dh2_6_a = value;
      break;
    case NDS32_OPERAND_DISP14 :
      fields->f_32t2_disp14 = value;
      break;
    case NDS32_OPERAND_DISP16 :
      fields->f_32t1_disp16 = value;
      break;
    case NDS32_OPERAND_DISP24 :
      fields->f_32t0_disp24 = value;
      break;
    case NDS32_OPERAND_DISP8 :
      fields->f_32t1_disp8 = value;
      break;
    case NDS32_OPERAND_DISP9 :
      fields->f_32t1_disp9 = value;
      break;
    case NDS32_OPERAND_DPREFST :
      fields->f_32t2_st4 = value;
      break;
    case NDS32_OPERAND_FDRA5 :
      fields->f_32_ra5 = value;
      break;
    case NDS32_OPERAND_FDRB5 :
      fields->f_32_rb5 = value;
      break;
    case NDS32_OPERAND_FDRT5 :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_FSRA5 :
      fields->f_32_ra5 = value;
      break;
    case NDS32_OPERAND_FSRB5 :
      fields->f_32_rb5 = value;
      break;
    case NDS32_OPERAND_FSRT5 :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_GROUPIDX :
      fields->f_32_group = value;
      break;
    case NDS32_OPERAND_HASH :
      break;
    case NDS32_OPERAND_HSDISP8 :
      fields->f_16_hsdisp8 = value;
      break;
    case NDS32_OPERAND_I2_1_A :
      fields->f_32_i2_1_a = value;
      break;
    case NDS32_OPERAND_IM1_4_A :
      fields->f_32_im1_4_a = value;
      break;
    case NDS32_OPERAND_IM5_I_A :
      fields->f_32_im5_i_a = value;
      break;
    case NDS32_OPERAND_IM5_M_A :
      fields->f_32_im5_m_a = value;
      break;
    case NDS32_OPERAND_IM6_I_0_A :
      fields->f_32_im6_i_0_a = value;
      break;
    case NDS32_OPERAND_IM6_I_1_A :
      fields->f_32_im6_i_1_a = value;
      break;
    case NDS32_OPERAND_IM6_M_0_A :
      fields->f_32_im6_m_0_a = value;
      break;
    case NDS32_OPERAND_IM6_M_1_A :
      fields->f_32_im6_m_1_a = value;
      break;
    case NDS32_OPERAND_IMM16_A :
      fields->f_32_imm16_a = value;
      break;
    case NDS32_OPERAND_IMM5U :
      fields->f_16_uimm5 = value;
      break;
    case NDS32_OPERAND_LSBLOC_A :
      fields->f_32_lsbloc_a = value;
      break;
    case NDS32_OPERAND_M2_3_A :
      fields->f_32_m2_3_a = value;
      break;
    case NDS32_OPERAND_M2_5_A :
      fields->f_32_m2_5_a = value;
      break;
    case NDS32_OPERAND_MASK4 :
      fields->f_32t5_mask4 = value;
      break;
    case NDS32_OPERAND_MFUSRIDX :
      fields->f_32_group_usr = value;
      break;
    case NDS32_OPERAND_MSYNCST :
      fields->f_32t3_ext3 = value;
      break;
    case NDS32_OPERAND_MTUSRIDX :
      fields->f_32_group_usr = value;
      break;
    case NDS32_OPERAND_R10A5_A :
      fields->f_32_r10a5_a = value;
      break;
    case NDS32_OPERAND_R10A5_A_B :
      fields->f_32_r10a5_a = value;
      break;
    case NDS32_OPERAND_R10A5_A_T :
      fields->f_32_r10a5_a = value;
      break;
    case NDS32_OPERAND_R10B5_A :
      fields->f_32_r10b5_a = value;
      break;
    case NDS32_OPERAND_R10B5_A_B :
      fields->f_32_r10b5_a = value;
      break;
    case NDS32_OPERAND_R10B5_A_T :
      fields->f_32_r10b5_a = value;
      break;
    case NDS32_OPERAND_R10C5_0_A :
      fields->f_32_r10c5_0_a = value;
      break;
    case NDS32_OPERAND_R10C5_1_A :
      fields->f_32_r10c5_1_a = value;
      break;
    case NDS32_OPERAND_R10C5_A :
      fields->f_32_r10c5_a = value;
      break;
    case NDS32_OPERAND_RA3 :
      fields->f_16_ra3 = value;
      break;
    case NDS32_OPERAND_RA4 :
      fields->f_16_ra4 = value;
      break;
    case NDS32_OPERAND_RA4_19_A :
      fields->f_32_ra4_19_a = value;
      break;
    case NDS32_OPERAND_RA5 :
      fields->f_32_ra5 = value;
      break;
    case NDS32_OPERAND_RA5_A :
      fields->f_32_ra5_a = value;
      break;
    case NDS32_OPERAND_RA5_A_B :
      fields->f_32_ra5_a = value;
      break;
    case NDS32_OPERAND_RA5_A_T :
      fields->f_32_ra5_a = value;
      break;
    case NDS32_OPERAND_RA5E :
      fields->f_16_ra5e = value;
      break;
    case NDS32_OPERAND_RA5H :
      fields->f_16_ra5h = value;
      break;
    case NDS32_OPERAND_RB3 :
      fields->f_16_rb3 = value;
      break;
    case NDS32_OPERAND_RB3_14_A :
      fields->f_32_rb3_14_a = value;
      break;
    case NDS32_OPERAND_RB5 :
      fields->f_32_rb5 = value;
      break;
    case NDS32_OPERAND_RB5_A :
      fields->f_32_rb5_a = value;
      break;
    case NDS32_OPERAND_RB5_A_B :
      fields->f_32_rb5_a = value;
      break;
    case NDS32_OPERAND_RB5_A_T :
      fields->f_32_rb5_a = value;
      break;
    case NDS32_OPERAND_RB5H :
      fields->f_16_rb5h = value;
      break;
    case NDS32_OPERAND_RB5P_A :
      fields->f_32_rb5p_a = value;
      break;
    case NDS32_OPERAND_RB5P_A_B :
      fields->f_32_rb5p_a = value;
      break;
    case NDS32_OPERAND_RB5P_A_T :
      fields->f_32_rb5p_a = value;
      break;
    case NDS32_OPERAND_RC1_5_A :
      fields->f_32_rc1_5_a = value;
      break;
    case NDS32_OPERAND_RC2_11_A :
      fields->f_32_rc2_11_a = value;
      break;
    case NDS32_OPERAND_RC4_A :
      fields->f_32_rc4_a = value;
      break;
    case NDS32_OPERAND_RC5_0_A :
      fields->f_32_rc5_0_a = value;
      break;
    case NDS32_OPERAND_RC5_1_A :
      fields->f_32_rc5_1_a = value;
      break;
    case NDS32_OPERAND_RD1 :
      fields->f_32_rd1 = value;
      break;
    case NDS32_OPERAND_RD1HL :
      fields->f_32_rd1hl = value;
      break;
    case NDS32_OPERAND_RD5_A :
      fields->f_32_rd5_a = value;
      break;
    case NDS32_OPERAND_REGLIST :
      fields->f_16_mask2 = value;
      break;
    case NDS32_OPERAND_RS5 :
      fields->f_32_rs5 = value;
      break;
    case NDS32_OPERAND_RT3 :
      fields->f_16_rt3 = value;
      break;
    case NDS32_OPERAND_RT3_7 :
      fields->f_16_rt3_7 = value;
      break;
    case NDS32_OPERAND_RT3E5 :
      fields->f_16_rt3 = value;
      break;
    case NDS32_OPERAND_RT4 :
      fields->f_16_rt4 = value;
      break;
    case NDS32_OPERAND_RT5 :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_RT5E :
      fields->f_16_rt5e = value;
      break;
    case NDS32_OPERAND_RT5H :
      fields->f_16_rt5h = value;
      break;
    case NDS32_OPERAND_RTH5 :
      fields->f_32_rt5 = value;
      break;
    case NDS32_OPERAND_RTL5 :
      fields->f_32_ra5 = value;
      break;
    case NDS32_OPERAND_SI :
      fields->f_32t3_sub10si = value;
      break;
    case NDS32_OPERAND_SIMM10 :
      fields->f_16_simm10 = value;
      break;
    case NDS32_OPERAND_SIMM11 :
      fields->f_32t2_simm11 = value;
      break;
    case NDS32_OPERAND_SIMM5H :
      fields->f_16_simm5 = value;
      break;
    case NDS32_OPERAND_SIMM5W :
      fields->f_16_simm5w = value;
      break;
    case NDS32_OPERAND_SLO12D :
      fields->f_32tx_slo12d = value;
      break;
    case NDS32_OPERAND_SLO12W :
      fields->f_32tx_slo12w = value;
      break;
    case NDS32_OPERAND_SLO15 :
      fields->f_32t2_slo15b = value;
      break;
    case NDS32_OPERAND_SLO15B :
      fields->f_32t2_slo15b = value;
      break;
    case NDS32_OPERAND_SLO15D :
      fields->f_32t2_slo15d = value;
      break;
    case NDS32_OPERAND_SLO15H :
      fields->f_32t2_slo15h = value;
      break;
    case NDS32_OPERAND_SLO15W :
      fields->f_32t2_slo15w = value;
      break;
    case NDS32_OPERAND_SLO17W :
      fields->f_32_slo17w = value;
      break;
    case NDS32_OPERAND_SLO18H :
      fields->f_32_slo18h = value;
      break;
    case NDS32_OPERAND_SLO19 :
      fields->f_32_slo19 = value;
      break;
    case NDS32_OPERAND_SLO20 :
      fields->f_32t1_slo20 = value;
      break;
    case NDS32_OPERAND_SR10 :
      fields->f_32_sr10 = value;
      break;
    case NDS32_OPERAND_STANDBYST :
      fields->f_32t4_ext2 = value;
      break;
    case NDS32_OPERAND_SUIMM5 :
      fields->f_16_suimm5 = value;
      break;
    case NDS32_OPERAND_SWID15 :
      fields->f_32t3_swid15 = value;
      break;
    case NDS32_OPERAND_SWID5 :
      fields->f_16_swid5 = value;
      break;
    case NDS32_OPERAND_SWID9 :
      fields->f_16_swid9 = value;
      break;
    case NDS32_OPERAND_TLBOPST :
      fields->f_32t4_ext5 = value;
      break;
    case NDS32_OPERAND_UHI20 :
      fields->f_32t1_uhi20 = value;
      break;
    case NDS32_OPERAND_UIMM12 :
      fields->f_32_12_12 = value;
      break;
    case NDS32_OPERAND_UIMM19 :
      fields->f_32_19_7 = value;
      break;
    case NDS32_OPERAND_UIMM3 :
      fields->f_16_uimm3 = value;
      break;
    case NDS32_OPERAND_UIMM3_10 :
      fields->f_16_uimm3_10 = value;
      break;
    case NDS32_OPERAND_UIMM5 :
      fields->f_32t3_uimm5 = value;
      break;
    case NDS32_OPERAND_UIMM5D :
      fields->f_16_uimm5d = value;
      break;
    case NDS32_OPERAND_UIMM5H :
      fields->f_16_uimm5 = value;
      break;
    case NDS32_OPERAND_UIMM6W :
      fields->f_16_uimm6w = value;
      break;
    case NDS32_OPERAND_UIMM8_S :
      fields->f_32_uimm8_s = value;
      break;
    case NDS32_OPERAND_UIMM_SR10 :
      fields->f_32_sr10 = value;
      break;
    case NDS32_OPERAND_ULO15 :
      fields->f_32t2_ulo15b = value;
      break;
    case NDS32_OPERAND_ULO15B :
      fields->f_32t2_ulo15b = value;
      break;
    case NDS32_OPERAND_ULO15D :
      fields->f_32t2_ulo15d = value;
      break;
    case NDS32_OPERAND_ULO15H :
      fields->f_32t2_ulo15h = value;
      break;
    case NDS32_OPERAND_ULO15W :
      fields->f_32t2_ulo15w = value;
      break;
    case NDS32_OPERAND_ULO3B :
      fields->f_16_ulo3b = value;
      break;
    case NDS32_OPERAND_ULO3H :
      fields->f_16_ulo3h = value;
      break;
    case NDS32_OPERAND_ULO3W :
      fields->f_16_ulo3w = value;
      break;
    case NDS32_OPERAND_ULO5 :
      fields->f_32t21_ulo5 = value;
      break;
    case NDS32_OPERAND_ULO7W :
      fields->f_16_ulo7w = value;
      break;
    case NDS32_OPERAND_USRIDX :
      fields->f_32_usr = value;
      break;

    default :
      /* xgettext:c-format */
      fprintf (stderr, _("Unrecognized field %d while setting vma operand.\n"),
		       opindex);
      abort ();
  }
}

/* Function to call before using the instruction builder tables.  */

void
nds32_cgen_init_ibld_table (CGEN_CPU_DESC cd)
{
  cd->insert_handlers = & nds32_cgen_insert_handlers[0];
  cd->extract_handlers = & nds32_cgen_extract_handlers[0];

  cd->insert_operand = nds32_cgen_insert_operand;
  cd->extract_operand = nds32_cgen_extract_operand;

  cd->get_int_operand = nds32_cgen_get_int_operand;
  cd->set_int_operand = nds32_cgen_set_int_operand;
  cd->get_vma_operand = nds32_cgen_get_vma_operand;
  cd->set_vma_operand = nds32_cgen_set_vma_operand;
}
