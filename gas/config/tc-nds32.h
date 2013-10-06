/* tc-nds32.h -- Header file for tc-nds32.c.

   Copyright 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013
   Free Software Foundation, Inc.
   Contributed by Andes Technology Corporation.

   This file is part of GAS.

   GAS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   GAS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GAS; see the file COPYING.  If not, write to the Free
   Software Foundation, 51 Franklin Street - Fifth Floor, Boston, MA
   02110-1301, USA.  */

#ifndef TC_NDS32
#define TC_NDS32

#include "bfd_stdint.h"

#define LISTING_HEADER \
  (target_big_endian ? "NDS32 GAS" : "NDS32 GAS Little Endian")

/* The target BFD architecture.  */
#define TARGET_ARCH		bfd_arch_nds32

/* Default to big endian. Please note that for Andes architecture,
   instructions are always in big-endian format. */
#ifndef TARGET_BYTES_BIG_ENDIAN
#define TARGET_BYTES_BIG_ENDIAN	1
#endif

/* This is used to construct expressions out of @GOTOFF, @PLT and @GOT
   symbols.  The relocation type is stored in X_md.  */
#define O_PIC_reloc O_md1

/*
 * as.c
 */
/* extend GAS command line option handling capability */
extern int nds32_parse_option (int, char *);
extern void nds32_after_parse_args (void);
/* The endianness of the target format may change based on command
   line arguments.  */
extern const char *nds32_target_format (void);
#define md_parse_option(optc, optarg)	nds32_parse_option (optc, optarg)
#define md_after_parse_args()		nds32_after_parse_args ()
#define TARGET_FORMAT nds32_target_format()


/* expr.c */
extern int nds32_parse_name (char const *, expressionS *, enum expr_mode, char *);
extern bfd_boolean nds32_allow_local_subtract (expressionS *, expressionS *, segT);
#define md_parse_name(name, exprP, mode, nextcharP) \
	nds32_parse_name (name, exprP, mode, nextcharP)
#define md_allow_local_subtract(lhs,rhs,sect)	nds32_allow_local_subtract (lhs, rhs, sect)

/*
 * dwarf2dbg.c
 */
#define DWARF2_USE_FIXED_ADVANCE_PC		1

/*
 * cgen.c
 */
extern int nds32_cgen_parse_fix_exp (int, expressionS *);
#define TC_CGEN_PARSE_FIX_EXP(opinfo, exp)	nds32_cgen_parse_fix_exp (opinfo, exp)
/* After creating a fixup for an instruction operand, we need to check for
   HI20 relocs and queue them up for later sorting.  */
#define md_cgen_record_fixup_exp		nds32_cgen_record_fixup_exp
/* Account for nop if 32 bit insn falls on odd halfword boundary.  TODO: Review this. */
#define TC_CGEN_MAX_RELAX(insn, len)		20

/*
 * write.c
 */
extern long nds32_pcrel_from_section (struct fix *, segT);
extern bfd_boolean nds32_fix_adjustable (struct fix *);
extern void nds32_frob_file (void);
extern void nds32_frob_file_before_fix (void);
extern void elf_nds32_final_processing (void);
extern int nds32_validate_fix_sub (struct fix *, segT);
extern int nds32_force_relocation (struct fix *);
extern void nds32_set_section_relocs(asection *, arelent ** , unsigned int );
/* Fill in rs_align_code fragments.  TODO: Review this. */
extern void nds32_handle_align (fragS *);
extern long nds32_relax_frag (segT, fragS *, long);
extern int tc_nds32_regname_to_dw2regnum (char *regname);
extern void tc_nds32_frame_initial_instructions (void);
#define MD_PCREL_FROM_SECTION(fix, sect)	nds32_pcrel_from_section(fix, sect)
#define TC_FINALIZE_SYMS_BEFORE_SIZE_SEG	0
#define tc_fix_adjustable(FIX)			nds32_fix_adjustable (FIX)
#define md_apply_fix(fixP, addn, seg)		nds32_apply_fix (fixP, addn, seg)
#define tc_frob_file()				nds32_frob_file ()
#define tc_frob_file_before_fix()		nds32_frob_file_before_fix ()
#define elf_tc_final_processing()		elf_nds32_final_processing ()
/* COLE: For DIFF relocations.
   The default behavior is inconsistent with the asm internal document.  */
#define TC_FORCE_RELOCATION_SUB_SAME(FIX, SEC)		\
  (! SEG_NORMAL (SEC) || TC_FORCE_RELOCATION (FIX))
#define TC_FORCE_RELOCATION(fix)		nds32_force_relocation (fix)
#define TC_VALIDATE_FIX_SUB(FIX,SEG)		nds32_validate_fix_sub (FIX,SEG)
#define SET_SECTION_RELOCS(sec, relocs, n)	nds32_set_section_relocs (sec, relocs, n)
/* Values passed to md_apply_fix don't include the symbol value.
   COLE: TODO: Review this.  */
#define MD_APPLY_SYM_VALUE(FIX)			0
#define HANDLE_ALIGN(f)				nds32_handle_align (f)
#undef DIFF_EXPR_OK				/* They should be fixed in linker.  */
#define md_relax_frag(segment, fragP, stretch)	nds32_relax_frag (segment, fragP, stretch)
#define WORKING_DOT_WORD			/* We don't need to handle .word strangely.  */
/* Using to chain fixup with previous fixup.  */
#define TC_FIX_TYPE struct fix*
#define TC_INIT_FIX_DATA(fixP) do 	\
{ 					\
  fixP->tc_fix_data=NULL; 		\
} while (0)

/*
 * read.c
 */
/* extend GAS macro handling capability */
extern void nds32_macro_start (void);
extern void nds32_macro_end (void);
extern void nds32_macro_info (void *macro);
extern void nds32_start_line_hook (void);
extern void nds32_elf_section_change_hook (void);
extern void md_begin (void);
extern void md_end (void);
extern int nds32_start_label (int, int);
extern void nds32_cleanup (void);
extern void nds32_flush_pending_output (void);
extern void nds32_cons_align (int n);
extern void nds32_check_label (symbolS *);
extern void nds32_frob_label (symbolS *);
void nds32_pre_do_align(int, char*, int, int);
void nds32_do_align(int);
#define md_macro_start()			nds32_macro_start()
#define md_macro_end()				nds32_macro_end()
#define md_macro_info(args)			nds32_macro_info(args)
#define TC_START_LABEL(C, S, STR)		(C == ':' && nds32_start_label (0, 0))
#define tc_check_label(label)			nds32_check_label (label)
#define tc_frob_label(label)			nds32_frob_label (label)
#define md_end					md_end
#define md_start_line_hook()			nds32_start_line_hook()
#define md_cons_align(n)			nds32_cons_align (n)
/* COLE: TODO: Review md_do_align. */
#define md_do_align(N, FILL, LEN, MAX, LABEL)	\
  nds32_pre_do_align(N, FILL, LEN, MAX);	\
  if ((N) > 1 && (subseg_text_p (now_seg)	\
      || strncmp(now_seg->name, ".gcc_except_table", sizeof(".gcc_except_table") - 1) == 0)) \
    nds32_do_align (N);				\
  goto LABEL;
#define md_elf_section_change_hook()		nds32_elf_section_change_hook()
#define md_flush_pending_output()		nds32_flush_pending_output ()
#define md_cleanup()				nds32_cleanup ()
#define LOCAL_LABELS_FB				1 /* Permit temporary numeric labels.  */

/*
 * frags.c
 */
#define NDS32_FRAG_FLAG_NUM 2
typedef struct nds32_frag_type {
  relax_substateT flag[NDS32_FRAG_FLAG_NUM];
  int insn_num;
  uint32_t insn32;
  /* To Save previos label fixup if existence.  */
  struct fix *fixup;
} nds32_frag_type;

extern void nds32_frag_init(fragS*);

#define TC_FRAG_TYPE				struct nds32_frag_type
#define TC_FRAG_INIT(fragP)			nds32_frag_init(fragP)

/*
 * CFI directive
 */
extern void nds32_elf_frame_initial_instructions(void);
extern int tc_nds32_regname_to_dw2regnum (char *regname);

#define TARGET_USE_CFIPOP			1
#define DWARF2_DEFAULT_RETURN_COLUMN		30
#define DWARF2_CIE_DATA_ALIGNMENT		-4
#define DWARF2_LINE_MIN_INSN_LENGTH		2

#define tc_regname_to_dw2regnum			tc_nds32_regname_to_dw2regnum
#define tc_cfi_frame_initial_instructions	tc_nds32_frame_initial_instructions

/*
 * COLE: TODO: Review These. They seem to be obsoleted.
 */
#if 1
#define TC_RELOC_RTSYM_LOC_FIXUP(FIX)				\
   ((FIX)->fx_addsy == NULL					\
    || (! S_IS_EXTERNAL ((FIX)->fx_addsy)			\
	&& ! S_IS_WEAK ((FIX)->fx_addsy)			\
	&& S_IS_DEFINED ((FIX)->fx_addsy)			\
	&& ! S_IS_COMMON ((FIX)->fx_addsy)))
#define TC_HANDLES_FX_DONE
/* This arranges for gas/write.c to not apply a relocation if
   obj_fix_adjustable() says it is not adjustable.  */
#define TC_FIX_ADJUSTABLE(fixP) obj_fix_adjustable (fixP)
#endif

/* Because linker may relax the code, assemble-time expression
   optimization is not allowed.  */
#define md_allow_eh_opt 0

#endif /* TC_NDS32 */
