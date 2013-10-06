/* tc-nds32.c -- Assemble for the NDS32 ISA

   Copyright 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013
   Free Software Foundation, Inc.
   Contributed by Andes Technology Corporation.

   This file is part of GAS.

   GAS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3 of the license, or
   (at your option) any later version.

   GAS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; see the file COPYING3. If not,
   see <http://www.gnu.org/licenses/>.  */

#include "as.h"
#include "safe-ctype.h"
#include "subsegs.h"
#include "symcat.h"
#include "dwarf2dbg.h"
#include "dw2gencfi.h"
#include "opcodes/nds32-desc.h"
#include "opcodes/nds32-opc.h"
#include "cgen.h"
#include "elf/nds32.h"
#include "opcode/nds32.h"
#include "bfd/elf32-nds32.h"
#include "hash.h"
#include "sb.h"
#include "macro.h"
#include "struc-symbol.h"

#include <stdio.h>

#ifdef CPU_CONFIG
#include <CPU_CONFIG>
#else
#define NDS32_ISA_DIV
#define NDS32_ISA_MAC_EXT
#define NDS32_ISA_16B_EXT
#define NDS32_ISA_PERF_EXT
#define NDS32_ISA_PERF2_EXT
#define NDS32_ISA_STRING_EXT
#define NDS32_ISA_BASELINE_V3
#define NDS32_ISA_DX_REGS
#define NDS32_ISA_AUDIO_EXT
#define NDS32_ISA_AUDIO_CONFIG 32
#define NDS32_ISA_COP_EXT
#define NDS32_ISA_IFC_EXT
#define NDS32_ISA_EX9_EXT
#endif

extern int nds32_cgen_get_int_operand (CGEN_CPU_DESC, int,
				       const CGEN_FIELDS *);
static int adj_label_pair (fragS * fragP);

/* GAS definitions.  */

/* Characters which start a comment.  */
const char comment_chars[] = "!";
/* Characters which start a comment when they appear at the start of a line.  */
const char line_comment_chars[] = "#!";
/* Characters which separate lines (null and newline are by default).  */
const char line_separator_chars[] = ";";
/* Characters which may be used as the exponent character
   in a floating point number.  */
const char EXP_CHARS[] = "eE";
/* Characters which may be used to indicate a floating point constant.  */
const char FLT_CHARS[] = "dDfF";


/* Relocations against symbols are done in two parts, with a 20-bit HI
   relocation and a 12-bit LO relocation.  This means that in order for the
   linker to handle carries correctly, it must be able to locate both the HI
   and the LO relocation.  This means that the relocations must appear in order
   in the relocation table.  */

/* In order to implement this, we keep track of each unmatched HI relocation.
   We then sort them so that they immediately precede the corresponding LO
   relocation.  */

struct nds32_hi_fixup
{
  struct nds32_hi_fixup *next;	/* Next HI fixup.  */
  fixS *fixp;			/* This fixup.  */
  segT seg;			/* The section this fixup is in.  */
};

/* The list of unmatched HI relocs.  */
static struct nds32_hi_fixup *nds32_hi_fixup_list;


/* Alignment support.  */

/* Save previous relaxed frag to align next label.  */
static fragS *prev_insn16 = NULL;
/* Save previous frag to align next label.  */
static fragS *prev_frag = NULL;
/* Save previous LABEL reloc for chaining to frag.  */
static fixS *prev_fixP = NULL;
/* Remember there is a label existing,
   and a reloc should be create in the following process.  */
static int label_exist = 0;
/* Remember the alignment of the pseudo label brought by .align.  */
static int label_align = 0;
static fixS *get_prev_fix (void);
static void set_prev_fix (fixS *);
static void nds32_insert_align_reloc (int);

static int relax_jal_bound = 3;
static int omit_frame_pointer = 1;
static int is_conservative_ifc = 0;

#define OPT_EXIT_FAILURE 3

/* The bit assignment is for different machines using different
   extensions.  For new machines, maybe simply or together the
   bits.  For example, someday in future, machine N3H is assigned
   to 0x10070002 means has all extensions listed below.  */
#define MACHINE_IS_N12  0x00000001
#define MACHINE_IS_N12H 0x00000002

/* Flags.  */

/* Non-zero if we are generating PIC code.  */
static int pic_code = 0;

/* Check configuration setting conflict.  */

static int elf_ver = E_NDS32_ELF_VER_1_4;

#if defined NDS32_ABI_2
static int abi_ver = E_NDS_ABI_AABI;
#elif defined NDS32_ABI_2FP
static int abi_ver = E_NDS_ABI_V2FP;
#else
static int abi_ver = E_NDS_ABI_V1;
#endif

/* Turn on the NO_MAC flag as default if not V2/V3/V3M arch.  */
#if !defined NDS32_ISA_BASELINE_V1
static int nds32_flags = 0;
#else
static int nds32_flags = E_NDS32_HAS_NO_MAC_INST;
#endif


/* Non-zero if warn when a high/shigh reloc has no matching low reloc.  Each
   high/shigh reloc must be paired with it's low cousin in order to properly
   calculate the addend in a relocatable link (since there is a potential
   carry from the low to the high/shigh).  This option is off by default
   though for user-written assembler code it might make sense to make the
   default be on (i.e. have gcc pass a flag to turn it off).  This warning
   must not be on for GCC created code as optimization may delete the low but
   not the high/shigh (at least we shouldn't assume or require it to).  */
static int warn_unmatched_high = 0;

static int enable_relax_relocs = 1;
static int enable_relax_ex9 = 0;
static int enable_relax_ifc = 0;
static int enable_relax_warning = 0;
static int multi_call_relax = 1;
static int pltgot_call_relax = 1;
static int hint_func_args = 0;	/* bit == 0: used; bit == 1: ignored */
static int use_hint_func_args = 1;
static int vec_size = 0;
/* If the assembly code is generated by compiler,
   it is supposed to have ".flag compiler_generated_asm" at beginning of the content.
   We have 'nds32_flag' to parse it and set this field to be nozero.  */
static int compiler_generated_asm = 0;

/* From now on, the default values for all extensions is based on target
   configuration - eht 08/07/07.  If any extension is turned on at target
   configuration time, the default value for this extension flag is 1.
   Customers may turn this flag off at compile/assemble time.  If any extension
   is turned off at target configuration time, the default value for this
   extension flag is 0.  Customers can turn this flag on at compile/assemble
   time, this can cause invalid instruction exception at runtime.  */

/* 1 if any extension option has been specified, in which case support for the
   extended NDS32 instruction set should be enabled.
   Default to all extensions turn on by target configuration.  */

/* 1 if -mno-16bit has been specified, in which case support for the base
   16-bit instruction set should be disabled.  */
#if defined NDS32_ISA_16B_EXT
int disable_16bit = 0;
static int saved_disable_16bit = 0;
#else
int disable_16bit = 1;
static int saved_disable_16bit = 1;
#endif

/* Non-zero if -mno-ext-perf is not specified, in which case support for
   extended NDS32 C/C++ performance instruction set should be enabled.  */
#if defined NDS32_ISA_PERF_EXT
static int enable_c_extension = 1;
#else
static int enable_c_extension = 0;
#endif

/* Non-zero if -mno-ext-perf is not specified, in which case support for
   extended NDS32 C/C++ performance instruction set should be enabled.  */
#if defined NDS32_ISA_PERF2_EXT
static int enable_c_extension2 = 1;
#else
static int enable_c_extension2 = 0;
#endif

#define ARCH_V1		bfd_mach_n1h
#define ARCH_V2		bfd_mach_n1h_v2
#define ARCH_V3		bfd_mach_n1h_v3
#define ARCH_V3M	bfd_mach_n1h_v3m

#if defined(NDS32_ISA_BASELINE_V1)
static int march_cpu_opt = ARCH_V1;
#elif defined(NDS32_ISA_BASELINE_V2)
static int march_cpu_opt = ARCH_V2;
#elif defined(NDS32_ISA_BASELINE_V3)
static int march_cpu_opt = ARCH_V3;
#elif defined(NDS32_ISA_BASELINE_V3M)
static int march_cpu_opt = ARCH_V3M;
#else
static int march_cpu_opt = ARCH_V3;
#endif

#if defined NDS32_ISA_DX_REGS && ! defined NDS32_ISA_BASELINE_V1
static int enable_dx_regs_extension = 1;
#else
static int enable_dx_regs_extension = 0;
#endif

/* Non-zero if -mext-dsp has been specified, in which case support for
   extended NDS32 DSP instruction set should be enabled.  */
#ifdef NDS32_ISA_DSP_EXT
static int enable_dsp_extension = 1;
#else
static int enable_dsp_extension = 0;
#endif

/* Non-zero if -mext-div is specified, in which case support for
   extended NDS32 DIV instruction set should be enabled.  */
#if defined NDS32_ISA_DIV || !defined NDS32_ISA_BASELINE_V1
static int enable_div_extension = 1;
#else
static int enable_div_extension = 0;
#endif

/* Non-zero if -mext-audio is specified, in which case support for
   extended NDS32 AUDIO instruction set should be enabled.  */
#if defined NDS32_ISA_AUDIO_EXT
# if defined NDS32_ISA_AUDIO_CONFIG
#  if (NDS32_ISA_AUDIO_CONFIG == 24) || (NDS32_ISA_AUDIO_CONFIG == 32) \
      || (NDS32_ISA_AUDIO_CONFIG == BOTH)
static int enable_audio_extension = 1;
#  else
#   error "Invalid NDS32_ISA_AUDIO_CONFIG value"
#  endif
# else
static int enable_audio_extension = 1;
# endif
#else /* No audio extension support.  */
static int enable_audio_extension = 0;
#endif

/* Non-zero if -mext-mac is specified, in which case support for
   extended NDS32 MAC/MUL instruction set should be enabled.  */
#if !defined NDS32_ISA_BASELINE_V1 \
    || defined NDS32_ISA_MAC_EXT || defined NDS32_ISA_AUDIO_EXT
static int enable_mac_extension = 1;
#else
static int enable_mac_extension = 0;
#endif

/* Non-zero if -mext-string is specified, in which case support for
   extended NDS32 STRING instruction set should be enabled.  */
#ifdef NDS32_ISA_STRING_EXT
static int enable_string_extension = 1;
#else
static int enable_string_extension = 0;
#endif

/* Non-zero if -mext-audio is specified, in which case support for
   extended NDS32 AUDIO instruction set should be enabled.  */
#ifdef NDS32_ISA_REDUCE_REGS
static int enable_reduce_regs = 1;
#else
static int enable_reduce_regs = 0;
#endif

/* Non-zero if -mfpu has been specified, in which case support for
   floating point processor instruction set should be enabled.  */
#if defined NDS32_ISA_FPU_DP_EXT
static int enable_fpu_dp_extension = 1;
static int enable_fpu_sp_extension = 1;
#else
# if defined NDS32_ISA_FPU_SP_EXT
static int enable_fpu_sp_extension = 1;
# else
static int enable_fpu_sp_extension = 0;
# endif
static int enable_fpu_dp_extension = 0;
#endif

/* Indicate if an FPU_COM instruction is found
   without previous non-FPU_COM instruction.  */
static int nds32_fpu_com = 0;

#if defined NDS32_ISA_FPU_MAC_EXT \
    && (defined NDS32_ISA_FPU_DP_EXT || defined NDS32_ISA_FPU_SP_EXT)
static int enable_fpu_mac_extension = 1;
#else
static int enable_fpu_mac_extension = 0;
#endif

#if defined NDS32_ISA_FPU_CONFIG && NDS32_ISA_FPU_CONFIG >= 0 \
	    && NDS32_ISA_FPU_CONFIG < 4
static int fs_reg_num = ((1 << (NDS32_ISA_FPU_CONFIG + 3)) > 32)
			? 32 : (1 << (NDS32_ISA_FPU_CONFIG + 3));
static int fd_reg_num = ((1 << (NDS32_ISA_FPU_CONFIG + 2)) > 32)
			? 32 : (1 << (NDS32_ISA_FPU_CONFIG + 2));
static int fpu_config = NDS32_ISA_FPU_CONFIG << E_NDS32_FPU_REG_CONF_SHIFT;
#else
static int fs_reg_num = 0;
static int fd_reg_num = 0;
static int fpu_config = 0;
#endif

/* Enable all extensions.  */
static int enable_all_ext = 0;

/* Non-zero if optimizations should be performed.  */
static int optimize = 0;
static int optimize_for_space = 0;
static int optimize_for_space_no_align = 0;

/* Back-to-back branch optimization.  */
static int b2bb_prev = 0;
static int opt_b2bb = 0;

typedef enum
{
  ALARM_BLOCK_NONE = 0,
  ALARM_BLOCK_BAD,
  ALARM_BLOCK_FATAL
} ALARM_BLOCK;
static ALARM_BLOCK alarm_block = ALARM_BLOCK_BAD;

static struct hash_control *insn_mnem_hash = NULL;
static struct hash_control *nds32_cgen_nomap_hash = NULL;


enum options
{
  OPTION_BIG = OPTION_MD_BASE,
  OPTION_LITTLE,
  OPTION_16BIT,
  OPTION_NO_16BIT,
  OPTION_EXT_ALL,
  OPTION_EXT_PERF,
  OPTION_NO_EXT_PERF,
  OPTION_EXT_DSP,
  OPTION_NO_EXT_DSP,
  OPTION_FPU_SP,
  OPTION_FPU_DP,
  OPTION_FPU_FMA,
  OPTION_NO_FPU_SP,
  OPTION_NO_FPU_DP,
  OPTION_NO_FPU_FMA,
  OPTION_FPU_FREG,
  OPTION_REDUCED_REGS,
  OPTION_NO_REDUCED_REGS,
  OPTION_EXT_AUDIO,
  OPTION_NO_EXT_AUDIO,
  OPTION_EXT_MAC,
  OPTION_NO_EXT_MAC,
  OPTION_DIV,
  OPTION_NO_DIV,
  OPTION_PIC_CODE,
  OPTION_NO_PIC_CODE,
  OPTION_OPTIMIZE,
  OPTION_OPTIMIZE_SPACE,
  OPTION_WARN_UNMATCHED,
  OPTION_NO_WARN_UNMATCHED,
  OPTION_CPU,
  OPTION_EXT_PERF2,
  OPTION_NO_EXT_PERF2,
  OPTION_EXT_STRING,
  OPTION_NO_EXT_STRING,
  OPTION_MARCH,
  OPTION_DX_REGS,
  OPTION_NO_DX_REGS,
  OPTION_NO_RELAX,
  OPTION_ABI,
  OPTION_RELAX_WARN,
  OPTION_NO_MULCALL_RELAX,
  OPTION_NO_PLTGOT_CALL_RELAX,
  OPTION_RELAX_JAL,
  OPTION_NO_HINT_FUNC_ARGS,
  OPTION_NO_OMIT_FP,
  OPTION_NO_CONSERVATIVE_IFC,
  OPTION_CONSERVATIVE_IFC,
  OPTION_ALARM_BLOCK,
  OPTION_B2BB,
  OPTION_NO_B2BB
};

#define NDS32_SHORTOPTS "G:O"
const char *md_shortopts = NDS32_SHORTOPTS;
struct option md_longopts[] = {
  {"big", no_argument, NULL, OPTION_BIG},
  {"little", no_argument, NULL, OPTION_LITTLE},
  {"EB", no_argument, NULL, OPTION_BIG},
  {"EL", no_argument, NULL, OPTION_LITTLE},
  {"meb", no_argument, NULL, OPTION_BIG},
  {"mel", no_argument, NULL, OPTION_LITTLE},
  {"mcpu", required_argument, NULL, OPTION_CPU},
  {"cpu", required_argument, NULL, OPTION_CPU},
  {"mabi", required_argument, NULL, OPTION_ABI},
  {"mpic", no_argument, NULL, OPTION_PIC_CODE},
  {"mno-pic", no_argument, NULL, OPTION_NO_PIC_CODE},
  {"O0", no_argument, NULL, OPTION_OPTIMIZE},
  {"O1", no_argument, NULL, OPTION_OPTIMIZE},
  {"O2", no_argument, NULL, OPTION_OPTIMIZE},
  {"O3", no_argument, NULL, OPTION_OPTIMIZE},
  {"Os", no_argument, NULL, OPTION_OPTIMIZE_SPACE},
  {"march", required_argument, NULL, OPTION_MARCH},
  {"misa", required_argument, NULL, OPTION_MARCH},

  {"mdx-regs", no_argument, NULL, OPTION_DX_REGS},
  {"mno-dx-regs", no_argument, NULL, OPTION_NO_DX_REGS},
  {"mno-16-bit", no_argument, NULL, OPTION_NO_16BIT},
  {"m16-bit", no_argument, NULL, OPTION_16BIT},
  /* These are options for extensions.  */
  {"mall-ext", no_argument, NULL, OPTION_EXT_ALL},
  {"mperf-ext", no_argument, NULL, OPTION_EXT_PERF},
  {"mno-perf-ext", no_argument, NULL, OPTION_NO_EXT_PERF},
  {"mperf2-ext", no_argument, NULL, OPTION_EXT_PERF2},
  {"mno-perf2-ext", no_argument, NULL, OPTION_NO_EXT_PERF2},
  {"mdsp-ext", no_argument, NULL, OPTION_EXT_DSP},
  {"mno-dsp-ext", no_argument, NULL, OPTION_NO_EXT_DSP},
  {"maudio-isa-ext", no_argument, NULL, OPTION_EXT_AUDIO},
  {"mno-audio-isa-ext", no_argument, NULL, OPTION_NO_EXT_AUDIO},
  {"mmac", no_argument, NULL, OPTION_EXT_MAC},
  {"mno-mac", no_argument, NULL, OPTION_NO_EXT_MAC},
  {"mstring-ext", no_argument, NULL, OPTION_EXT_STRING},
  {"mno-string-ext", no_argument, NULL, OPTION_NO_EXT_STRING},
  {"mdiv", no_argument, NULL, OPTION_DIV},
  {"mno-div", no_argument, NULL, OPTION_NO_DIV},
  {"mfpu-sp-ext", no_argument, NULL, OPTION_FPU_SP},
  {"mno-fpu-sp-ext", no_argument, NULL, OPTION_NO_FPU_SP},
  {"mfpu-dp-ext", no_argument, NULL, OPTION_FPU_DP},
  {"mno-fpu-dp-ext", no_argument, NULL, OPTION_NO_FPU_DP},
  {"mfpu-fma", no_argument, NULL, OPTION_FPU_FMA},
  {"mno-fpu-fma", no_argument, NULL, OPTION_NO_FPU_FMA},
  {"mfpu-freg", required_argument, NULL, OPTION_FPU_FREG},
  {"mreduced-regs", no_argument, NULL, OPTION_REDUCED_REGS},
  {"mfull-regs", no_argument, NULL, OPTION_NO_REDUCED_REGS},
  /* These are relaxation options.  */
  {"mno-relax", no_argument, NULL, OPTION_NO_RELAX},
  {"mb2bb", no_argument, NULL, OPTION_B2BB},
  {"mno-b2bb", no_argument, NULL, OPTION_NO_B2BB},

  /* These are internal options.  */
  {"mno-conservative-ifc", no_argument, NULL, OPTION_NO_CONSERVATIVE_IFC},
  {"mconservative-ifc", no_argument, NULL, OPTION_CONSERVATIVE_IFC},
  {"mrelax-warning", no_argument, NULL, OPTION_RELAX_WARN},
  {"mno-mulcall", no_argument, NULL, OPTION_NO_MULCALL_RELAX},
  {"mno-pltgotcall", no_argument, NULL, OPTION_NO_PLTGOT_CALL_RELAX},
  {"mrelax-jal", required_argument, NULL, OPTION_RELAX_JAL},
  {"mno-hint-func-args", no_argument, NULL, OPTION_NO_HINT_FUNC_ARGS},
  {"mno-omit-fp", no_argument, NULL, OPTION_NO_OMIT_FP},

  /* These are obsolete options.  Remove them in the future.  */
  {"KPIC", no_argument, NULL, OPTION_NO_PIC_CODE},
  {"mbaseline", required_argument, NULL, OPTION_MARCH},
  {"warn-unmatched-high", no_argument, NULL, OPTION_WARN_UNMATCHED},
  {"Wuh", no_argument, NULL, OPTION_WARN_UNMATCHED},
  {"no-warn-unmatched-high", no_argument, NULL, OPTION_NO_WARN_UNMATCHED},
  {"Wnuh", no_argument, NULL, OPTION_NO_WARN_UNMATCHED},
  {"malarm-block", required_argument, NULL, OPTION_ALARM_BLOCK},
  {"mno-16bit", no_argument, NULL, OPTION_NO_16BIT},
  {"m16bit", no_argument, NULL, OPTION_16BIT},
  {"mext-all", no_argument, NULL, OPTION_EXT_ALL},
  {"mext-perf", no_argument, NULL, OPTION_EXT_PERF},
  {"mno-ext-perf", no_argument, NULL, OPTION_NO_EXT_PERF},
  {"mext-perf2", no_argument, NULL, OPTION_EXT_PERF2},
  {"mno-ext-perf2", no_argument, NULL, OPTION_NO_EXT_PERF2},
  {"mext-dsp", no_argument, NULL, OPTION_EXT_DSP},
  {"mno-ext-dsp", no_argument, NULL, OPTION_NO_EXT_DSP},
  {"mext-audio", no_argument, NULL, OPTION_EXT_AUDIO},
  {"mno-ext-audio", no_argument, NULL, OPTION_NO_EXT_AUDIO},
  {"mext-mac", no_argument, NULL, OPTION_EXT_MAC},
  {"mno-ext-mac", no_argument, NULL, OPTION_NO_EXT_MAC},
  {"mext-string", no_argument, NULL, OPTION_EXT_STRING},
  {"mno-ext-string", no_argument, NULL, OPTION_NO_EXT_STRING},
  {"mext-fpu-sp", no_argument, NULL, OPTION_FPU_SP},
  {"mext-fpu-dp", no_argument, NULL, OPTION_FPU_DP},
  {"mext-fpu-mac", no_argument, NULL, OPTION_FPU_FMA},
  {"mno-ext-fpu-sp", no_argument, NULL, OPTION_NO_FPU_SP},
  {"mno-ext-fpu-dp", no_argument, NULL, OPTION_NO_FPU_DP},
  {"mno-ext-fpu-mac", no_argument, NULL, OPTION_NO_FPU_FMA},
  {"mconfig-fpu", required_argument, NULL, OPTION_FPU_FREG},
  {"mreduce-regs", no_argument, NULL, OPTION_REDUCED_REGS},
  {"mno-reduce-regs", no_argument, NULL, OPTION_NO_REDUCED_REGS},
  {NULL, no_argument, NULL, 0}
};

size_t md_longopts_size = sizeof (md_longopts);

/* strcasestr is not supported by MinGW toolchain.
   This function is copied from tc-rx.c.  */

static char *
nds32_strcasestr (const char *string, const char *sub)
{
  int subl;
  int strl;

  if (!sub || !sub[0])
    return (char *) string;

  subl = strlen (sub);
  strl = strlen (string);

  while (strl >= subl)
    {
      /* strncasecmp is in libiberty.  */
      if (strncasecmp (string, sub, subl) == 0)
	return (char *) string;

      string++;
      strl--;
    }
  return NULL;
}

/* md_after_parse_args ()

   GAS will call md_after_parse_args whenever it is defined.
   This function checks any conflicting options specified.  */

void
nds32_after_parse_args (void)
{
  int err = had_errors ();

  if (march_cpu_opt == ARCH_V1)
    {
      /* V1 soft core.  */
      if (enable_dx_regs_extension)
	as_bad (_("CPU option -mdx-reg conflicts with V1 Architecture"));
      if (had_errors () != err)
	exit (OPT_EXIT_FAILURE);
    }

  if (march_cpu_opt == ARCH_V1)
    {
      nds32_flags = E_NDS32_HAS_NO_MAC_INST;
    }

  if (enable_all_ext)
    {
      enable_c_extension = 1;
      enable_c_extension2 = 1;
      enable_fpu_sp_extension = 1;
      enable_fpu_dp_extension = 1;
      enable_fpu_mac_extension = 1;
      enable_audio_extension = 1;
      enable_string_extension = 1;
      enable_mac_extension = 1;
      enable_div_extension = 1;
      enable_dx_regs_extension = 1;
    }

  if (disable_16bit)
    {
      /* Not able to optimize at all.  */
      optimize = 0;
      optimize_for_space = 0;
      optimize_for_space_no_align = 0;
    }

  if (relax_jal_bound < 0)
    {
      as_bad (_("relax jal bound cannot be negative."));
      exit (OPT_EXIT_FAILURE);
    }
}

/* This function is called when printing usage message (--help).  */

void
md_show_usage (FILE *stream)
{
  fprintf (stream, "\
  -EL, -mel or -little    Produce little endian output\n\
  -EB, -meb or -big       Produce big endian output\n\
  -O                      Optimize for performance\n\
  -Os                     Optimize for space\n\
  -mcpu=CPU               Assemble for CPU CPU\n\
  -misa=ISA               Assemble for ISA\n\
                            v1, v2, v3, v3m)\n\
  -mabi=ABI               Override default ABI flag in ELF header\n\
                            1, 2, 2fp\n\
  -mall-ext               Allow all instruction extensions\n\
  -m[no-]16-bit           Disable/enable 16-bit instructions\n\
  -m[no-]perf-ext         Disable/enable Performance Extension\n\
  -m[no-]perf2-ext        Disable/enable Performance Extension V2\n\
  -m[no-]string-ext       Disable/enable String Extension\n\
  -m[no-]dsp-ext          Disable/enable DSP Extension\n\
  -m[no-]mac              Disable/enable Multiply/Multiply-Add instructions\n\
                            (using register d0/d1)\n\
  -m[no-]div              Disable/enable DIV/DIVS instructions instructions\n\
                            (using register d0/d1)\n\
  -m[no-]audio-isa-ext    Disable/enable AUDIO ISA Extension\n\
  -m[no-]fpu-sp-ext       Disable/enable FPU SP Extension\n\
  -m[no-]fpu-dp-ext       Disable/enable FPU DP Extension\n\
  -m[no-]fpu-fma          Disable/enable FPU Fused-Multiply-Add instructions\n\
  -mfpu-freg=FREG         Specify a FPU configuration\n\
                            0      8 SP /  4 DP registers\n\
                            1     16 SP /  8 DP registers\n\
                            2     32 SP / 16 DP registers\n\
                            3     32 SP / 32 DP registers\n\
  -mreduced-regs          Only reduced-set registers are allowed\n\
  -mfull-regs             Full-set registers are allowed\n\
  -m[no-]dx-regs          Reject/allow d0/d1 registers\n\
  -mpic                   Generate PIC\n\
\n\
Relaxation related options:\n\
  -mno-relax              Suppress relaxation for this file\n\
  -mb2bb                  Back-to-back branch optimization\n\
");
}

/* Instruction operand access macros.  */
#define CGEN_FIELDS_RT5(fields)       ((fields).f_32_rt5)
#define CGEN_FIELDS_RA5(fields)       ((fields).f_32_ra5)
#define CGEN_FIELDS_RB5(fields)       ((fields).f_32_rb5)
#define CGEN_FIELDS_RT5E(fields)    ((fields).f_16_rt5e)
#define CGEN_FIELDS_RA5E(fields)    ((fields).f_16_ra5e)
#define CGEN_FIELDS_RD1HL(fields)     ((fields).f_32_rd1hl)
#define CGEN_FIELDS_DISP24(fields)    ((fields).f_32t0_disp24)
#define CGEN_FIELDS_SIMM20(fields)    ((fields).f_32t1_slo20)
#define CGEN_FIELDS_UHI20(fields)     ((fields).f_32t1_uhi20)
#define CGEN_FIELDS_DISP16(fields)    ((fields).f_32t1_disp16)
#define CGEN_FIELDS_SLO15D(fields)    ((fields).f_32t2_slo15d)
#define CGEN_FIELDS_ULO15D(fields)    ((fields).f_32t2_ulo15d)
#define CGEN_FIELDS_SLO15W(fields)    ((fields).f_32t2_slo15w)
#define CGEN_FIELDS_ULO15W(fields)    ((fields).f_32t2_ulo15w)
#define CGEN_FIELDS_SLO15H(fields)    ((fields).f_32t2_slo15h)
#define CGEN_FIELDS_ULO15H(fields)    ((fields).f_32t2_ulo15h)
#define CGEN_FIELDS_SLO15B(fields)    ((fields).f_32t2_slo15b)
#define CGEN_FIELDS_ULO15B(fields)    ((fields).f_32t2_ulo15b)
#define CGEN_FIELDS_DISP14(fields)    ((fields).f_32t2_disp14)
#define CGEN_FIELDS_32UIMM5(fields)   ((fields).f_32t3_uimm5)
#define CGEN_FIELDS_RT5H(fields)      ((fields).f_16_rt5h)
#define CGEN_FIELDS_RA5H(fields)      ((fields).f_16_ra5h)
#define CGEN_FIELDS_RB5H(fields)      ((fields).f_16_rb5h)
#define CGEN_FIELDS_RT4(fields)       ((fields).f_16_rt4)
#define CGEN_FIELDS_RA4(fields)       ((fields).f_16_ra4)
#define CGEN_FIELDS_RT3(fields)       ((fields).f_16_rt3)
#define CGEN_FIELDS_RT37(fields)      ((fields).f_16_rt3_7)
#define CGEN_FIELDS_RA3(fields)       ((fields).f_16_ra3)
#define CGEN_FIELDS_RB3(fields)       ((fields).f_16_rb3)
#define CGEN_FIELDS_UIMM3(fields)     ((fields).f_16_uimm3)
#define CGEN_FIELDS_16UIMM5(fields)   ((fields).f_16_uimm5)
#define CGEN_FIELDS_SIMM5(fields)     ((fields).f_16_simm5)
#define CGEN_FIELDS_UIMM7(fields)     ((fields).f_16_rt3_7)
#define CGEN_FIELDS_HSDISP8(fields)   ((fields).f_16_hsdisp8)
#define CGEN_FIELDS_MASK4(fields)     ((fields).f_32t5_mask4)
#define CGEN_FIELDS_USRIDX(fields)    ((fields).f_32_usr)
#define CGEN_FIELDS_GROUPIDX(fields)  ((fields).f_32_group)
#define CGEN_FIELDS_SIMM11(fields)    ((fields).f_32t2_simm11)

/* Fragment subtype definitions.  */

/* It's an 16-bit frag if bit 0 and bit 10 are both 0.  */
/* frag[0] */
#define RELAX_RT_MASK             0xf8000000  /* bit 31..27 for register rt5.  */
#define RELAX_RA_MASK             0x07c00000  /* bit 26..22 for register ra5.  */
#define RELAX_RB_MASK             0x003e0000  /* bit 21..17 for register rb5.  */
#define RELAX_RELAXABLE_MASK      0x00010000  /* bit 16; frag is relaxable.  */
#define RELAX_RELAXED_MASK        0x00008000  /* bit 15; frag relaxed.  */
#define RELAX_FORCE_NO_16BIT_MASK 0x00004000  /* bit 14; only 32-bit instruction is used in frag.  */
#define RELAX_SEQ_TYPE_MASK       0x00003c00  /* bit 13..10 ; branch code seq.  */
#define RELAX_BRANCH_MASK         0x00000001  /* bit 0; set if branch instruction.  */
/* flag[1] */
#define RELAX_SIMM11_MASK         0xffe00000  /* bit 31..21 for register simm11.  */
#define RELAX_OPC_NUM_MASK        0xffffffff  /* bit 31..0; opcode number.  */

/* Relaxed branch sequence types:

   BR_UCOND_CALL_S16M
      jal   label

   BR_UCOND_CALL_U4G
      sethi $ta,   hi20(label)
      ori   $ta,   [$ta + lo12(label)]
      jral  $ta ; linker may contract it to 16-bit for label alignment

   BR_COND_CALL_S64K
      bgezal   rt,   label ; or bltzal rt,   label

   BR_COND_CALL_S16M
      bltz  rt,   $1 ; or bgez   rt, $1
      jal   label
      $1:

   BR_COND_CALL_U4G
      bltz  rt,   $1 ; or bgez   rt, $1
      sethi $ta,   hi20(label)
      ori   $ta,   [$ta + lo12(label)]
      jral  $ta ; linker may contract it to 16-bit for label alignment
      $1:

   BR_UCOND_BR_S256,
      j     label ; linker may contract it to 16-bit for label alignment

   BR_UCOND_BR_S16M,
      j     label

   BR_UCOND_BR_U4G,
      sethi $ta,   hi20(label)
      ori   $ta,   [$ta + lo12(label)]
      jr    $ta ; linker may contract it to 16-bit for label alignment

   BR_COND_BR_S256
      beqs38   rt3,  label ; or other 16-bit conditional branches

   BR_COND_BR_S16K,
      beq   rt5,  ra5,  label ; or  bne   rt5, ra5,   label

   BR_COND_BR_S64K,
      beqz  rt5,  label ; or other 32-bit conditional branch against 0

   BR_COND_BR_S16M,
      bnes38   rt3,  label
      j        label
      $1:

   BR_COND_BR_U4G
      bnes38   rt3,  label
      sethi $ta,   hi20(label)
      ori   $ta,   [$ta + lo12(label)]
      jral  $ta ; linker may contract it to 16-bit for label alignment
 */

/* Relaxed memory access with label.

   MEM_ACC_LONG
      sethi    rt,   hi20(label)
      lwi      rt,   [rt + lo12(label)]

   MEM_ACC_SHORT
      lwi      rt,   [$gp + sda(label)]
 */

typedef enum br_insn_type
{
  BR_UCOND_BR,		/* Unconditional branch.  */
  BR_COND_BR,		/* Conditional branch.  */
  BR_UCOND_CALL,	/* Unconditional call.  */
  BR_COND_CALL		/* Conditional call.  */
} BR_INSN_TYPE;

typedef enum br_range_type
{
  BR_RANGE_S256,	/* PC relative -256 to 254.  */
  BR_RANGE_S16K,	/* PC relative -16K to 16K - 2.  */
  BR_RANGE_S64K,	/* PC relative -64K to 64K - 2.  */
  BR_RANGE_S16M,	/* PC relative -16M to 16M - 2.  */
  BR_RANGE_U4G		/* Absolute 0 to 4G - 2.  */
} BR_RANGE_TYPE;

typedef enum br_seq_type
{
  BR_SEQ_NONE,
  BR_UCOND_CALL_S16M,	/* PC relative -16M to 16M -2 unconditional call.  */
  BR_UCOND_CALL_U4G,	/* Absolute 0 to 4G - 2 unconditional call.  */
  BR_COND_CALL_S64K,	/* PC relative -64K to 64K -2 conditional call.  */
  BR_COND_CALL_S16M,	/* PC relative -16M to 16M -2 conditional call.  */
  BR_COND_CALL_U4G,	/* Absolute 0 to 4G - 2 conditional call.  */
  BR_UCOND_BR_S256,	/* PC relative -256 to 254 unconditional branch.  */
  BR_UCOND_BR_S16M,	/* PC relative -16M to 16M -2 unconditional branch.  */
  BR_UCOND_BR_U4G,	/* Absolute 0 to 4G - 2 unconditional branch.  */
  BR_COND_BR_S256,	/* PC relative -256 to 254 conditional branch.  */
  BR_COND_BR_S16K,	/* PC relative -16K to 16K - 2 conditional branch.  */
  BR_COND_BR_S64K,	/* PC relative -64K to 64K - 2 conditional branch.  */
  BR_COND_BR_S16M,	/* PC relative -16M to 16M - 2 conditional branch.  */
  BR_COND_BR_U4G	/* Absolute 0 to 4G - 2 conditional branch.  */
} BR_SEQ_TYPE;

typedef enum ls_type
{
  LS_SHORT,
  LS_LONG
} LS_TYPE;

/* Set branch code of fr_subtype.  */
#define SET_BR_CODE(code)  ((code & 0xf) << 10)

/* Is a frag relaxable?  */
#define RELAX_RELAXABLE(fragp) \
	(fragp->tc_frag_data.flag[0] & RELAX_RELAXABLE_MASK)
/* Is a frag relaxed?  */
#define RELAX_RELAXED(fragp) \
	(fragp->tc_frag_data.flag[0] & RELAX_RELAXED_MASK)
/* Force frag to use 32-bit instruction?  */
#define RELAX_USE_32BIT(fragp) \
	(fragp->tc_frag_data.flag[0] & RELAX_FORCE_NO_16BIT_MASK)
/* Mark a frag as relaxable.  */
#define RELAX_SET_RELAXABLE(fragp) \
	(fragp->tc_frag_data.flag[0] |= RELAX_RELAXABLE_MASK)

/* Mark a frag as not relaxable.  */
#define RELAX_CLEAR_RELAXABLE(fragp) \
	(fragp->tc_frag_data.flag[0] &= (~RELAX_RELAXABLE_MASK))

/* Mark a frag as relaxed.  */
#define RELAX_SET_RELAXED(fragp) \
	(fragp->tc_frag_data.flag[0] |= RELAX_RELAXED_MASK)

#define RELAX_SET_INSN(fragp, insn) \
	do { fragp->tc_frag_data.insn32 = insn; } while (0)
#define RELAX_GET_INSN(fragp) fragp->tc_frag_data.insn32

/* Mark a frag as not relaxed.  */
#define RELAX_CLEAR_RELAXED(fragp) \
	(fragp->tc_frag_data.flag[0] &= (~RELAX_RELAXED_MASK))

/* Get branch bit of an instruction.  */
#define RELAX_BRANCH(fragp) \
	(((fragp)->tc_frag_data.flag[0] & RELAX_BRANCH_MASK) >> 0)

/* Get original rt5 register.  */
#define RELAX_RT(fragp) (((fragp)->tc_frag_data.flag[0] & RELAX_RT_MASK) >> 27)

/* Get original ra5 register.  */
#define RELAX_RA(fragp) (((fragp)->tc_frag_data.flag[0] & RELAX_RA_MASK) >> 22)

/* Get original rb5 register.  */
#define RELAX_RB(fragp) (((fragp)->tc_frag_data.flag[0] & RELAX_RB_MASK) >> 17)

/* Get original simm11 immediate (beqc/bnec).  */
#define RELAX_SIMM11(fragp) \
	(long) __SEXT ((((fragp)->tc_frag_data.flag[1] & RELAX_SIMM11_MASK) >> 21), 11)

/* Get original opcode number of a branch.  */
#define RELAX_32(fragp) (((fragp)->tc_frag_data.flag[0] & RELAX_32_MASK) >> 16)

/* Get original opcode number of a branch.  */
#define RELAX_OPC_NUM(fragp) (((fragp)->tc_frag_data.insn_num & RELAX_OPC_NUM_MASK))

/* Get relaxation code sequence of a branch.  */
#define RELAX_SEQ_TYPE(fragp) \
	(((fragp)->tc_frag_data.flag[0] & RELAX_SEQ_TYPE_MASK) >> 10)

/* Set all relaxation flag.  */
#define RELAX_SET_FRAG_TC_FLAGS(fragp, flagp)	\
do {						\
  int __i = 0;					\
  for (;__i < NDS32_FRAG_FLAG_NUM;__i++) {	\
    fragp->tc_frag_data.flag[__i] = flagp[__i];	\
  }						\
} while (0)

/* Set relaxation flag.  */
#define RELAX_SET_FRAG_TC_FLAG(nump, fragp, flagp) \
	(fragp->tc_frag_data.flag[nump] = flagp)

/* Get relaxation flag.  */
#define RELAX_GET_FRAG_TC_FLAG(nump, fragp) \
	(fragp->tc_frag_data.flag[nump])

/* Set relaxation opcode number.  */
#define RELAX_SET_FRAG_TC_OPCNUM(fragp, opcnum) \
	((fragp)->tc_frag_data.insn_num = \
		(((fragp)->tc_frag_data.insn_num & (~RELAX_OPC_NUM_MASK)) \
		 | (opcnum & RELAX_OPC_NUM_MASK)))

#define SET_ADDEND( size, convertible, optimize, insn16_on ) \
   (((size) & 0xff) | ((convertible) ? 1 << 31 : 0) \
    | ((optimize) ? 1<< 30 : 0) | (insn16_on ? 1 << 29 : 0))

void
nds32_frag_init (fragS *fragp)
{
  int i = 0;

  for (; i < NDS32_FRAG_FLAG_NUM; i++)
    fragp->tc_frag_data.flag[i] = 0;
  fragp->tc_frag_data.insn_num = 0;
  RELAX_SET_INSN (fragp, 0);
  fragp->tc_frag_data.fixup = NULL;
}

typedef struct insn16_to_32
{
  CGEN_INSN_TYPE insn16;
  CGEN_INSN_TYPE insn32;
} INSN_MAP_ENTRY;

INSN_MAP_ENTRY insn16_to_32[] = {
  {NDS32_INSN_MOV55, NDS32_INSN_ORI},
  {NDS32_INSN_MOVI55, NDS32_INSN_MOVI},
  {NDS32_INSN_ADDI45, NDS32_INSN_ADDI},
  {NDS32_INSN_ADD45, NDS32_INSN_ADD},
  {NDS32_INSN_SUBI45, NDS32_INSN_ADDI},
  {NDS32_INSN_SUB45, NDS32_INSN_SUB},
  {NDS32_INSN_SRAI45, NDS32_INSN_SRAI},
  {NDS32_INSN_SRLI45, NDS32_INSN_SRLI},
  {NDS32_INSN_SLLI333, NDS32_INSN_SLLI},
  {NDS32_INSN_ADDI333, NDS32_INSN_ADDI},
  {NDS32_INSN_ADD333, NDS32_INSN_ADD},
  {NDS32_INSN_SUBI333, NDS32_INSN_ADDI},
  {NDS32_INSN_SUB333, NDS32_INSN_SUB},
  {NDS32_INSN_LWI333, NDS32_INSN_LWI},
  {NDS32_INSN_LWI333_BI, NDS32_INSN_LWI_BI},
  {NDS32_INSN_LHI333, NDS32_INSN_LHI},
  {NDS32_INSN_LBI333, NDS32_INSN_LBI},
  {NDS32_INSN_SWI333, NDS32_INSN_SWI},
  {NDS32_INSN_SWI333_BI, NDS32_INSN_SWI_BI},
  {NDS32_INSN_SHI333, NDS32_INSN_SHI},
  {NDS32_INSN_SBI333, NDS32_INSN_SBI},
  {NDS32_INSN_LWI450, NDS32_INSN_LWI},
  {NDS32_INSN_SWI450, NDS32_INSN_SWI},
  {NDS32_INSN_LWI37, NDS32_INSN_LWI},
  {NDS32_INSN_SWI37, NDS32_INSN_SWI},
  {NDS32_INSN_BEQZ38, NDS32_INSN_BEQZ},
  {NDS32_INSN_BNEZ38, NDS32_INSN_BNEZ},
  {NDS32_INSN_BEQS38, NDS32_INSN_BEQ},
  {NDS32_INSN_BNES38, NDS32_INSN_BNE},
  {NDS32_INSN_J8, NDS32_INSN_J},
  {NDS32_INSN_JR5, NDS32_INSN_JR},
  {NDS32_INSN_RET5, NDS32_INSN_RET},
  {NDS32_INSN_JRAL5, NDS32_INSN_JRAL},
  {NDS32_INSN_SLTI45, NDS32_INSN_SLTI},
  {NDS32_INSN_SLTSI45, NDS32_INSN_SLTSI},
  {NDS32_INSN_SLT45, NDS32_INSN_SLT},
  {NDS32_INSN_SLTS45, NDS32_INSN_SLTS},
  {NDS32_INSN_BEQZS8, NDS32_INSN_BEQZ},
  {NDS32_INSN_BNEZS8, NDS32_INSN_BNEZ},
  {NDS32_INSN_BREAK16, NDS32_INSN_BREAK}
};

static int is_convertible (fragS *);

static int
get_frag_insn_size (fragS *fragP, int offset)
{
  uint16_t insn16;
  char *where;

  if (fragP->fr_fix < 2)
    return 0;

  where = fragP->fr_literal + offset;

  /* Offset must be even number.  */
  gas_assert ((offset & 1) == 0);
  insn16 = bfd_getb16 (where);

  if ((insn16 & 0x8000) >> 15)
    {
      /* 2 byte insn, is it relaxed?  */
      if (offset == fragP->fr_fix - 2
	  && (RELAX_RELAXED (fragP) || RELAX_BRANCH (fragP)))
	return 4;
      else
	return 2;
    }
  else
    return 4;
}

static valueT
md_chars_to_number (char *buf, int n)
{
  valueT result = 0;
  unsigned char *where = (unsigned char *) buf;

  if (target_big_endian)
    {
      while (n--)
	{
	  result <<= 8;
	  result |= (*where++ & 255);
	}
    }
  else
    {
      while (n--)
	{
	  result <<= 8;
	  result |= (where[n] & 255);
	}
    }

  return result;
}

/* The assembler tries to optimize the code size through relaxation
   processing, so that conversion from 32-bit instruction to
   corresponding 16-bit instruction is done whenever possible.  */

static int
convert_32_to_16 (fragS *fragP, uint16_t *pinsn,
		  relax_substateT *subtype, int *pinsn_type)
{
  char *buf;
  uint16_t insn16 = 0;
  uint32_t insn = 0;
  int insn_type = 0;

  /* FIXME: This piece of code is borrowed from bfd/elf32-nds32.c
     This function converts a 32-bit instruction to 16-bit one.  */

  if (subtype[0] & RELAX_FORCE_NO_16BIT_MASK)
    return 0;

  /* FIXME: The way to check instruction availability can be dangerous
     if this instruction doesn't exist in a future ISA,
     but anyway, there is no way for assembler to know.
     Besides, I don't think conversion should be done in assembler,
     since CGEN is the only one who knows the encoding details.
     This function brings maintenance issues.  */

  if (fragP->fr_symbol != NULL)
    {
      /* Instruction with symbol is not convertible
	 because symbol is relocatable.  */
      return 0;
    }

  /* Where is the 32-bit instruction.  */
  if (fragP == frag_now)
    {
      buf = fragP->fr_literal + frag_now_fix_octets () - 4;
    }
  else
    {
      /* Frag has been closed, so fragP->fr_fix is valid.  */
      buf = fragP->fr_literal + fragP->fr_fix - 4;
    }

  /* Get instruction contents.  */
  insn = bfd_getb32 (buf);

  nds32_convert_32_to_16 (stdoutput, insn, &insn16, &insn_type);

  if (insn16 != 0)
    {
      if (insn_type == 0)
	as_warn (_("Internal warning: Forget to set insn_num in "
		   "convert_32_to_16 (insn=0x%x).\n"), (int) insn);
      if (pinsn)
	{
	  *pinsn = insn16;
	  *pinsn_type = insn_type;
	}

      if (subtype)
	{
	  *pinsn = insn16;
	  *pinsn_type = insn_type;
	}
      return 1;
    }
  else
    {
      return 0;
    }
}

/* This function convert 16-bit instruction to 32-bit.  */

static int
convert_16_to_32 (fragS *fragP, uint32_t *insn_p)
{
  /* Where is the 16-bit instruction.  */
  uint16_t insn16;

  insn16 = bfd_getb16 (fragP->fr_literal + fragP->fr_fix - 2);
  if (RELAX_GET_INSN (fragP))
    {
      *insn_p = RELAX_GET_INSN (fragP);
      return TRUE;
    }

  return nds32_convert_16_to_32 (stdoutput, insn16, insn_p);
}

static char *nds32_cgen_nomap_table[][2] = {
  {"neg", "subri"},
  {"zeb", "andi"},
  {"lbi.p", "lbi.bi"},
  {"lb.p", "lb.bi"},
  {"lhi.p", "lhi.bi"},
  {"lh.p", "lh.bi"},
  {"lwi.p", "lwi.bi"},
  {"lw.p", "lw.bi"},
  {"lbsi.p", "lbsi.bi"},
  {"lbs.p", "lbs.bi"},
  {"lhsi.p", "lhsi.bi"},
  {"lhs.p", "lhs.bi"},
  {"sbi.p", "sbi.bi"},
  {"sb.p", "sb.bi"},
  {"shi.p", "shi.bi"},
  {"sh.p", "sh.bi"},
  {"swi.p", "swi.bi"},
  {"sw.p", "sw.bi"},
  {"nop", "srli"},
  {"nop16", "srli45"},
  {"beq_r", "beq"},
  {"bne_r", "bne"},
  {"beqz_r", "beqz"},
  {"bnez_r", "bnez"},
  {"bgez_r", "bgez"},
  {"bltz_r", "bltz"},
  {"bgtz_r", "bgtz"},
  {"blez_r", "blez"},
  {"beqs38_r", "beqs38"},
  {"bnes38_r", "bnes38"},
  {"beqz38_r", "beqz38"},
  {"bnez38_r", "bnez38"},
  {"beqzs8_r", "beqzs8"},
  {"bnezs8_r", "bnezs8"},
  {"bgezal_r", "bgezal"},
  {"bltzal_r", "bltzal"},
  {"j_r", "j"},
  {"j8_r", "j8"},
  {"jal_r", "jal"},
  {"jral_r", "jral"},
  {"jral5_r", "jral5"},
  {"flsi1.bi", "flsi.bi"},
  {"ifret16", "ifret"},
  {"beqc_r", "beqc"},
  {"bnec_r", "bnec"},
  {0, 0}
};

static int forbid_insn_num[MAX_INSNS];

static void
init_forbid_insn_num (void)
{
  int i;

  /* 0: Do nothing.
     1: Forbid and alarm.
     2: Do translation if could.  */

  for (i = NDS32_INSN_INVALID; i < MAX_INSNS; i++)
    {
      /* legacy macro expand instructions
	 * beq/bne
	 * beqz/bnez/bgez/bltz/bgtz/blez
	 * bgezal/bltzal  */
      if ((i >= NDS32_INSN_BEQ && i <= NDS32_INSN_BLTZAL)
	  /* beqs38/beqz38/bnes38/bnez38  */
	  || (i >= NDS32_INSN_BEQZ38 && i <= NDS32_INSN_BNES38)
	  || i == NDS32_INSN_BEQZS8
	  || i == NDS32_INSN_BNEZS8
	  || i == NDS32_INSN_BEQC
	  || i == NDS32_INSN_BNEC
	  || i == NDS32_INSN_JRAL5)
	{
	  forbid_insn_num[i] = 2;
	}
      else
	forbid_insn_num[i] = 0;

      if (march_cpu_opt != ARCH_V3M)
	continue;

      /* lmwa/smwa  */
      else if (i >= NDS32_INSN_LMWA_BI && i <= NDS32_INSN_SMWA_ADM)
	forbid_insn_num[i] = 1;
      /* mulr64/mulsr64  */
      else if (i == NDS32_INSN_MULR64 || i == NDS32_INSN_MULSR64)
	forbid_insn_num[i] = 1;

      /* Dx related instructions.
	 * madd32/madd64/madds64
	 * msub32/msub64/msubs64
	 * mult32/mult64/mults64  */
      else if (i >= NDS32_INSN_MULTS64 && i <= NDS32_INSN_MSUB32)
	forbid_insn_num[i] = 1;
      /* divs/div  */
      else if (i == NDS32_INSN_DIVS || i == NDS32_INSN_DIV)
	forbid_insn_num[i] = 1;
      /* mfusr/mtusr  */
      else if (i == NDS32_INSN_MFUSR || i == NDS32_INSN_MTUSR)
	forbid_insn_num[i] = 1;
      /* jrnez/jralnez/add5.pc  */
      else if (i == NDS32_INSN_JRNEZ || i == NDS32_INSN_JRALNEZ
	       || i == NDS32_INSN_ADD5_PC)
	forbid_insn_num[i] = 1;
      /* tlbop/cctl  */
      else if (i == NDS32_INSN_CCTL)
	forbid_insn_num[i] = 1;
      /* dprefi/dpref  */
      else if (i >= NDS32_INSN_DPREFI_D && i <= NDS32_INSN_DPREF)
	forbid_insn_num[i] = 1;
      /* llw/scw  */
      else if (i == NDS32_INSN_LLW || i == NDS32_INSN_SCW)
	forbid_insn_num[i] = 1;
      /* lwup/swup  */
      else if (i == NDS32_INSN_LWUP || i == NDS32_INSN_SWUP)
	forbid_insn_num[i] = 1;
      /* trap/teqz/tnez  */
      else if (i >= NDS32_INSN_TRAP && i <= NDS32_INSN_TNEZ)
	forbid_insn_num[i] = 1;
      /* lbup/sbup  */
      else if (i == NDS32_INSN_LBUP || i == NDS32_INSN_SBUP)
	forbid_insn_num[i] = 1;
      /* jr.toff/jr.itoff  */
      /* ret.toff/ret.itoff  */
      else if (i >= NDS32_INSN_JR_ITOFF && i <= NDS32_INSN_RET_TOFF)
	forbid_insn_num[i] = 1;
      /* jral.iton/jral.ton  */
      else if (i == NDS32_INSN_JRAL_ITON || i == NDS32_INSN_JRAL_TON)
	forbid_insn_num[i] = 1;
    }
}

static void
alarm_forbid_insn (char const *opcode)
{
  if (alarm_block == ALARM_BLOCK_NONE)
    ;
  else if (alarm_block == ALARM_BLOCK_BAD)
    as_bad ("[V3m error]: %s is unsupported instruction", opcode);
  else if (alarm_block == ALARM_BLOCK_FATAL)
    as_fatal ("[V3m error]: %s is unsupported instruction", opcode);
}

static int
check_forbid_insn (char const *opcode, int insn_num)
{
  static int forbid_insn_not_init = 1;
  CGEN_INSN *insn_entry;

  /* 0: Assemble instruction
     1: Forbid and alarm
     2: Do translation if could.  */

  if (forbid_insn_not_init)
    {
      init_forbid_insn_num ();
      forbid_insn_not_init = 0;
    }

  if (insn_num < 0)
    {
      if (opcode)
	{
	  insn_entry = hash_find (insn_mnem_hash, opcode);
	  if (insn_entry)
	    {
	      if (forbid_insn_num[insn_entry->base->num] == 1)
		alarm_forbid_insn (opcode);
	      return forbid_insn_num[insn_entry->base->num];
	    }
	}
      return 2;
    }

  if (forbid_insn_num[insn_num] == 1)
    alarm_forbid_insn (opcode);
  return forbid_insn_num[insn_num];
}

static CGEN_INSN_TABLE *
nds32_init_insn_num_map (void)
{
  unsigned int i;
  CGEN_INSN_TABLE *insn_table;
  CGEN_INSN_TABLE *macro_insn_table;
  CGEN_INSN *insn_entry;
  char *alias_name;

  insn_table = &gas_cgen_cpu_desc->insn_table;
  macro_insn_table = &gas_cgen_cpu_desc->macro_insn_table;

  if (insn_mnem_hash)
    return NULL;

  insn_mnem_hash = hash_new ();
  for (i = 0; insn_table && i < insn_table->num_init_entries; i++)
    {
      if (insn_table->init_entries[i].base == NULL
	  || insn_table->init_entries[i].base->mnemonic == NULL)
	continue;
      hash_insert (insn_mnem_hash, insn_table->init_entries[i].base->mnemonic,
		   (void *) &insn_table->init_entries[i]);
    }

  nds32_cgen_nomap_hash = hash_new ();
  for (i = 0; nds32_cgen_nomap_table[i][0] != NULL; i++)
    {
      hash_insert (nds32_cgen_nomap_hash, nds32_cgen_nomap_table[i][0],
		   (void *) nds32_cgen_nomap_table[i][1]);
    }

  for (i = 0; macro_insn_table && i < macro_insn_table->num_init_entries; i++)
    {
      if (macro_insn_table->init_entries[i].base == NULL
	  || macro_insn_table->init_entries[i].base->mnemonic == NULL)
	continue;
      insn_entry = hash_find (insn_mnem_hash,
		   macro_insn_table->init_entries[i].base->mnemonic);

      if (insn_entry == NULL)
	{
	  alias_name = hash_find (nds32_cgen_nomap_hash,
		       macro_insn_table->init_entries[i].base->mnemonic);
	  /* COLE: Why alias matters assembler?  */
	  if (alias_name == NULL)
	    continue;

	  insn_entry = hash_find (insn_mnem_hash, alias_name);
	  if (insn_entry)
	    hash_insert (insn_mnem_hash,
			 macro_insn_table->init_entries[i].base->mnemonic,
			 insn_entry);
	}
      else if (insn_entry->base->num == -1)
	{
	  fprintf (stderr, "Mnemonic \"%s\" not found in instruction table\n",
		   insn_entry->base->mnemonic);
	}
    }
  return insn_table;
}

/* Andes built-in functions for macro expansion.

   We support up to MAX_MACRO_LEVEL levels of nested macro expansion.  Also,
   each level can have its own local variables and labels.

   Keep track of local labels so we can substitute them before GAS sees them
   since macros use their own 'namespace' for local labels and a separate hash.

   We do our own local label handling because it's subtly different from the
   stock GAS handling.

   We use our own macro nesting counter, since GAS overloads it when expanding
   other things (like conditionals and repeat loops).  */

/* Registers are colored.  */
#define ADDRESSABLE_3BIT 0x1
#define ADDRESSABLE_4BIT 0x2
#define ADDRESSABLE_5BIT 0x4

typedef struct
{
  const char *name;
  const int index;
  const int flag;
  /* 0x01 - 3-bit only.
     0x02 - 4-bit only.
     0x04 - 5-bit only.
     0x06 - 4/5-bit only.
     0x07 - all 3 modes.  */
} nds32_regs;

nds32_regs reduce_regs[] = {
  /* Standard names.  */
  {"$r0", 0, 7}, {"$r1", 1, 7}, {"$r2", 2, 7}, {"$r3", 3, 7},
  {"$r4", 4, 7}, {"$r5", 5, 7}, {"$r6", 6, 7}, {"$r7", 7, 7},
  {"$r8", 8, 6}, {"$r9", 9, 6}, {"$r10", 10, 6},
  {"$r15", 15, 4},
  {"$r28", 28, 4}, {"$r29", 29, 4}, {"$r30", 30, 4}, {"$r31", 31, 4},
  /* Names for parameter passing.  */
  {"$a0", 0, 7}, {"$a1", 1, 7}, {"$a2", 2, 7}, {"$a3", 3, 7},
  {"$a4", 4, 7}, {"$a5", 5, 7},
  /* Names reserved for 5-bit addressing only.  */
  {"$s0", 6, 4}, {"$s1", 7, 4}, {"$s2", 8, 4}, {"$s3", 9, 4},
  {"$s4", 10, 4},
  {"$s9", 28, 4},
  {"$ta", 15, 4},
  {"$fp", 28, 4}, {"$gp", 29, 4}, {"$lp", 30, 4}, {"$sp", 31, 4},
  /* Names reserved for 4-bit addressing only.  */
  {"$h0", 0, 2}, {"$h1", 1, 2}, {"$h2", 2, 2}, {"$h3", 3, 2},
  {"$h4", 4, 2}, {"$h5", 5, 2}, {"$h6", 6, 2}, {"$h7", 7, 2},
  {"$h8", 8, 2}, {"$h9", 9, 2}, {"$h10", 10, 2},
  /* Names reserved for 3-bit addressing only.  */
  {"$o0", 0, 1}, {"$o1", 1, 1}, {"$o2", 2, 1}, {"$o3", 3, 1},
  {"$o4", 4, 1}, {"$o5", 5, 1}, {"$o6", 6, 1}, {"$o7", 7, 1},
  /* Names reserved for multiply and divide.  */
  {"$d0", 0, 7}, {"$d0.lo", 0, 7}, {"$d0.hi", 0, 7}, {"$d1", 0, 7},
  {"$d1.lo", 0, 7}, {"$d1.hi", 0, 7},
  {NULL, 0, 0}
};

nds32_regs fs_regs[] = {
  /* Standard names.  */
  {"$fs0", 0, 7}, {"$fs1", 1, 7}, {"$fs2", 2, 7}, {"$fs3", 3, 7},
  {"$fs4", 4, 7}, {"$fs5", 5, 7}, {"$fs6", 6, 7}, {"$fs7", 7, 7},
  {"$fs8", 8, 6}, {"$fs9", 9, 6}, {"$fs10", 10, 6}, {"$fs11", 11, 6},
  {"$fs12", 12, 4}, {"$fs13", 13, 4}, {"$fs14", 14, 4}, {"$fs15", 15, 4},
  {"$fs16", 16, 6}, {"$fs17", 17, 6}, {"$fs18", 18, 6}, {"$fs19", 19, 6},
  {"$fs20", 20, 4}, {"$fs21", 21, 4}, {"$fs22", 22, 4}, {"$fs23", 23, 4},
  {"$fs24", 24, 4}, {"$fs25", 25, 4}, {"$fs26", 26, 4}, {"$fs27", 27, 4},
  {"$fs28", 28, 4}, {"$fs29", 29, 4}, {"$fs30", 30, 4}, {"$fs31", 31, 4},
  {NULL, 0, 0}
};

nds32_regs fd_regs[] = {
  /* Standard names.  */
  {"$fd0", 0, 7}, {"$fd1", 1, 7}, {"$fd2", 2, 7}, {"$fd3", 3, 7},
  {"$fd4", 4, 7}, {"$fd5", 5, 7}, {"$fd6", 6, 7}, {"$fd7", 7, 7},
  {"$fd8", 8, 6}, {"$fd9", 9, 6}, {"$fd10", 10, 6}, {"$fd11", 11, 6},
  {"$fd12", 12, 4}, {"$fd13", 13, 4}, {"$fd14", 14, 4}, {"$fd15", 15, 4},
  {"$fd16", 16, 6}, {"$fd17", 17, 6}, {"$fd18", 18, 6}, {"$fd19", 19, 6},
  {"$fd20", 20, 4}, {"$fd21", 21, 4}, {"$fd22", 22, 4}, {"$fd23", 23, 4},
  {"$fd24", 24, 4}, {"$fd25", 25, 4}, {"$fd26", 26, 4}, {"$fd27", 27, 4},
  {"$fd28", 28, 4}, {"$fd29", 29, 4}, {"$fd30", 30, 4}, {"$fd31", 31, 4},
  {NULL, 0, 0}
};

nds32_regs regs[] = {
  /* Standard names.  */
  {"$r0", 0, 7}, {"$r1", 1, 7}, {"$r2", 2, 7}, {"$r3", 3, 7},
  {"$r4", 4, 7}, {"$r5", 5, 7}, {"$r6", 6, 7}, {"$r7", 7, 7},
  {"$r8", 8, 6}, {"$r9", 9, 6}, {"$r10", 10, 6}, {"$r11", 11, 6},
  {"$r12", 12, 4}, {"$r13", 13, 4}, {"$r14", 14, 4}, {"$r15", 15, 4},
  {"$r16", 16, 6}, {"$r17", 17, 6}, {"$r18", 18, 6}, {"$r19", 19, 6},
  {"$r20", 20, 4}, {"$r21", 21, 4}, {"$r22", 22, 4}, {"$r23", 23, 4},
  {"$r24", 24, 4}, {"$r25", 25, 4}, {"$r26", 26, 4}, {"$r27", 27, 4},
  {"$r28", 28, 4}, {"$r29", 29, 4}, {"$r30", 30, 4}, {"$r31", 31, 4},
  /* Names for parameter passing.  */
  {"$a0", 0, 7}, {"$a1", 1, 7}, {"$a2", 2, 7}, {"$a3", 3, 7},
  {"$a4", 4, 7}, {"$a5", 5, 7},
  /* Names reserved for 5-bit addressing only.  */
  {"$s0", 6, 4}, {"$s1", 7, 4}, {"$s2", 8, 4}, {"$s3", 9, 4},
  {"$s4", 10, 4}, {"$s5", 11, 4}, {"$s6", 12, 4}, {"$s7", 13, 4},
  {"$s8", 14, 4}, {"$s9", 28, 4},
  {"$ta", 15, 4},
  {"$t0", 16, 4}, {"$t1", 17, 4}, {"$t2", 18, 4}, {"$t3", 19, 4},
  {"$t4", 20, 4}, {"$t5", 21, 4}, {"$t6", 22, 4}, {"$t7", 23, 4},
  {"$t8", 24, 4}, {"$t9", 25, 4},
  {"$p0", 26, 4}, {"$p1", 27, 4},
  {"$fp", 28, 4}, {"$gp", 29, 4}, {"$lp", 30, 4}, {"$sp", 31, 4},
  /* Names reserved for 4-bit addressing only.  */
  {"$h0", 0, 2}, {"$h1", 1, 2}, {"$h2", 2, 2}, {"$h3", 3, 2},
  {"$h4", 4, 2}, {"$h5", 5, 2}, {"$h6", 6, 2}, {"$h7", 7, 2},
  {"$h8", 8, 2}, {"$h9", 9, 2}, {"$h10", 10, 2}, {"$h11", 11, 2},
  {"$h12", 16, 2}, {"$h13", 17, 2}, {"$h14", 18, 2}, {"$h15", 19, 2},
  /* Names reserved for 3-bit addressing only.  */
  {"$o0", 0, 1}, {"$o1", 1, 1}, {"$o2", 2, 1}, {"$o3", 3, 1},
  {"$o4", 4, 1}, {"$o5", 5, 1}, {"$o6", 6, 1}, {"$o7", 7, 1},
  {NULL, 0, 0}
};

#define MAX_MACRO_LEVEL    32
static int macro_level = 0;
static struct hash_control *local_label_hash[MAX_MACRO_LEVEL];
/* Prevent infinite recurse.  */
static struct hash_control *builtin_recurse_hash;
/* Level 0 is the main substitution symbol table.  */
static struct hash_control *builtin_hash[MAX_MACRO_LEVEL];
/* Registers.  */
static struct hash_control *reg5_hash;
static struct hash_control *reg4_hash;
static struct hash_control *reg3_hash;
static struct hash_control *fs5_hash;
static struct hash_control *fd5_hash;

static struct hash_control *bfdsym_hash;

/* This ensures that all new labels are unique.  */
static int local_label_id = 0;

/* Built-in substitution symbol functions.  */
typedef struct
{
  char *name;
  int (*proc) (char *, char *);
  int nargs;
} builtin_proc_entry;

/* This function looks up the substitution string replacement for the given
   symbol.  It starts with the innermost macro substitution table given and work
   outwards.  */

static char *
builtin_lookup (char *name, int nest_level)
{
  char *value;

  value = hash_find (builtin_hash[nest_level], name);

  if (value || nest_level == 0)
    return value;

  return builtin_lookup (name, nest_level - 1);
}

/* This function replaces the given substitution string.  We start at the
   innermost macro level, so that existing locals remain local.
   Note: we're treating macro arguments identically to .var's.  */

static void
builtin_create_or_replace (char *name, char *value)
{
  int i;

  for (i = macro_level; i >= 0; i--)
    {
      if (hash_find (builtin_hash[i], name))
	{
	  hash_replace (builtin_hash[i], name, value);
	  return;
	}
    }
  hash_insert (builtin_hash[0], name, value);
}

/* Mutually recursive with builtin_get_arg.  */
static char *builtin_substitute (char *line, int forced);

/* This function returns copy of line up to closing quote if quote found;
   otherwise up until terminator.  If it's a string, pass as-is; otherwise
   attempt substitution symbol replacement on the value.  */

static char *
builtin_get_arg (char *line, char *terminators, char **str, int nosub)
{
  char *ptr = line;
  char *endp;
  int is_string = *line == '"';
  int is_char = ISDIGIT (*line);

  if (is_char)
    {
      /* What other form of digits?  */
      if (ptr[0] == '0' && (TOLOWER (ptr[1]) == 'x' || TOLOWER (ptr[1]) == 'b'))
	ptr += 2;
      while (ISXDIGIT (*ptr))
	++ptr;
      if (*ptr == 'b' || *ptr == 'f')
	/* Local label? Accept it.  */
	++ ptr;
      endp = ptr;
      *str = xmalloc (ptr - line + 1);
      strncpy (*str, line, ptr - line);
      (*str)[ptr - line] = 0;
    }
  else if (is_string)
    {
      char *savedp = input_line_pointer;
      char *tmp;
      int len;

      input_line_pointer = ptr;
      tmp = demand_copy_C_string (&len);
      endp = input_line_pointer;
      input_line_pointer = savedp;

      /* Do forced substitutions if requested.  */
      if (!nosub && *tmp == ':')
	{
	  *str = builtin_substitute (tmp, 1);
	  if (*str != tmp)
	    free (tmp);
	}
      else
	*str = tmp;
    }
  else
    {
      char *term = terminators;
      char *value = NULL;
      int need_right_pren = 0;

      while (1)
	{
	  while (*ptr && *ptr != *term)
	    {
	      if (!*term)
		{
		  term = terminators;
		  if (*ptr == '(')
		    need_right_pren++;
		  ++ptr;
		}
	      else
		++term;
	    }

	  if (*ptr == 0)
	    {
	      break;
	    }
	  else if (need_right_pren)
	    {
	      term = terminators;
	      if (*ptr == ')')
		need_right_pren--;
	      ptr++;
	    }
	  else
	    {
	      break;
	    }
	}

      endp = ptr;
      *str = xmalloc (ptr - line + 1);
      strncpy (*str, line, ptr - line);
      (*str)[ptr - line] = 0;
      /* Do simple substitution, if available.  */
      if (!nosub && (value = builtin_lookup (*str, macro_level)) != NULL)
	*str = value;
    }

  return endp;
}

/* This functions does substitution-symbol replacement on the given line
   (recursively).  It returns the argument if no substitution was done.  It also
   looks for built-in functions ($func (arg)) and local labels.  If FORCED is
   set, look for forced substitutions of the form ':SYMBOL:'.  */

static char *
builtin_substitute (char *line, int forced)
{
  /* For each apparent symbol, see if it's a substitution symbol,
     and if so, replace it in the input.  */
  char *replacement;		/* Current replacement for LINE.  */
  char *head;			/* Start of line.  */
  char *ptr;			/* Current examination point.  */
  int changed = 0;		/* Did we make a substitution?  */
  int eval_line = 0;		/* Is this line a .eval/.asg statement?  */
  int eval_symbol = 0;		/* Are we in the middle of the symbol for .eval/.asg?  */
  char *eval_end = NULL;
  int recurse = 1;
  int inRI5 = 0;
  char *tmp;

  /* If it's a macro definition, don't do substitution on the argument names.
     If it's a character string, don't do substitution on the arguments.  */
  if (nds32_strcasestr (line, ".macro") || nds32_strcasestr (line, ".ascii")
      || nds32_strcasestr (line, ".string") || nds32_strcasestr (line, ".asciz"))
    return line;

  /* Watch out for .eval, so that we avoid doing substitution on the
     symbol being assigned a value.  */
  if (nds32_strcasestr (line, ".eval") || nds32_strcasestr (line, ".asg"))
    eval_line = 1;

  /* Work with a copy of the input line.  */
  replacement = xmalloc (strlen (line) + 4);
  strcpy (replacement, line);

  ptr = head = replacement;

  while (!is_end_of_line[(unsigned char) *ptr])
    {
      int current_char = *ptr;

      /* Need to update this since LINE may have been modified.  */
      if (eval_line)
	eval_end = strrchr (ptr, ',');

      /* Replace triple double quotes with bounding quote/escapes.  */
      if (current_char == '"' && ptr[1] == '"' && ptr[2] == '"')
	{
	  ptr[1] = '\\';
	  tmp = strstr (ptr + 2, "\"\"\"");
	  if (tmp)
	    tmp[0] = '\\';
	  changed = 1;
	}

      /* Flag when we've reached the symbol part of .eval/.asg.  */
      if (eval_line && ptr >= eval_end)
	eval_symbol = 1;

      /* For each apparent symbol, see if it's a substitution symbol,
	 and if so, replace it in the input.  */
      if ((forced && current_char == ':')
	  || (!forced && is_name_beginner (current_char)))
	{
	  char *name;		/* Symbol to be replaced.  */
	  char *savedp = input_line_pointer;
	  int c;
	  char *value = NULL;
	  char *tail;		/* Rest of line after symbol.  */

	  /* Skip the colon.  */
	  if (forced)
	    ++ptr;

	  name = input_line_pointer = ptr;
	  c = get_symbol_end ();

	  /* Avoid infinite recursion; if a symbol shows up a second time for
	     substitution, leave it as is.  */
	  if (hash_find (builtin_recurse_hash, name) == NULL)
	    value = builtin_lookup (name, macro_level);
	  else
	    as_warn (_("%s symbol recursion stopped at "
		       "second appearance of '%s'"),
		     forced ? "Forced substitution" : "Substitution", name);
	  ptr = tail = input_line_pointer;
	  input_line_pointer = savedp;

	  /* Check for local labels; replace them with the appropriate substitution.  */
	  if ((*name == '$' && ISDIGIT (name[1]) && name[2] == '\0')
	      || name[strlen (name) - 1] == '?')
	    {
	      /* Use an existing identifier for that label if, available, or
		 create a new, unique identifier.  */
	      value = hash_find (local_label_hash[macro_level], name);
	      if (value == NULL)
		{
		  char digit[11];
		  char *namecopy = strcpy (xmalloc (strlen (name) + 1), name);

		  value = strcpy (xmalloc (strlen (name) + sizeof (digit) + 1),
			    name);
		  if (*value != '$')
		    value[strlen (value) - 1] = '\0';
		  sprintf (digit, ".%d", local_label_id++);
		  strcat (value, digit);
		  hash_insert (local_label_hash[macro_level], namecopy,
			       value);
		}
	      /* Indicate where to continue looking for substitutions.  */
	      ptr = tail;
	    }
	  /* Check for built-in subsym and math functions.  */
	  else if (value != NULL && *name == '$')
	    {
	      if (macro_level == 0)
		{
		  as_bad (_("Built-in function is for writing macro only"));
		  break;
		}
	      else
		{
		  builtin_proc_entry *entry = (builtin_proc_entry *) value;
		  char *arg1, *arg2 = NULL;
		  int val;

		  *ptr = c;
		  if (entry == NULL)
		    {
		      as_bad (_("Unrecognized substitution symbol function"));
		      break;
		    }
		  else if (*ptr != '(')
		    {
		      as_bad (_("Missing '(' after substitution symbol function"));
		      break;
		    }
		  ++ptr;

		  if (entry->nargs == 0)
		    arg1 = NULL;
		  else
		    {
		      int arg_type[2] = {0};
		      int ismember = !strcmp (entry->name, "$ismember");

		      arg_type[0] = *ptr == '"';

		      /* Parse one or two args, which must be a substitution
			 symbol, string or a character-string constant.
			 For all functions, a string or substitution symbol may be
			 used, with the following exceptions:
			 firstch/lastch: 2nd arg must be character constant
			 ismember: both args must be substitution symbols.  */
		      ptr = builtin_get_arg (ptr, ",)", &arg1, ismember);
		      if (!arg1)
			break;
		      if (entry->nargs == 2)
			{
			  if (*ptr++ != ',')
			    {
			      as_bad (_("Function expects two arguments"));
			      break;
			    }
			  /* Character constants are converted to numerics
			     by the preprocessor.  */
			  arg_type[1] = (ISDIGIT (*ptr)) ? 2 : (*ptr == '"');
			  ptr = builtin_get_arg (ptr, ")", &arg2, ismember);
			}

		      /* Args checking.  */
		      if ((!strcmp (entry->name, "$firstch")
			   || !strcmp (entry->name, "$lastch"))
			  && arg_type[1] != 2)
			{
			  as_bad (_("Expecting character constant argument"));
			  break;
			}
		      if (ismember && (arg_type[0] != 0 || arg_type[1] != 0))
			{
			  as_bad (_("Both arguments must be substitution symbols"));
			  break;
			}
		    }
		  if (*ptr++ != ')')
		    {
		      as_bad (_("Extra junk in function call, expecting ')'"));
		      break;
		    }
		  val = (*entry->proc) (arg1, arg2);
		  value = xmalloc (64);
		  sprintf (value, "%d", val);

		  /* Fix things up to replace the entire expression,
		     not just the function name.  */
		  tail = ptr;
		  c = *tail;
		}
	    }

	  if (value != NULL && !eval_symbol)
	    {
	      /* Replace the symbol with its string replacement and
		 continue.  Recursively replace VALUE until either no
		 substitutions are performed, or a substitution that has been
		 previously made is encountered again.  */

	      /* Put the symbol into the recursion hash table so we only
		 try to replace a symbol once.  */
	      if (recurse)
		{
		  char *old_value = value;

		  hash_insert (builtin_recurse_hash, name, name);
		  value = builtin_substitute (old_value, macro_level > 0);
		  if (old_value != value)
		    free (old_value);
		  hash_delete (builtin_recurse_hash, name, FALSE);
		}

	      /* Temporarily zero-terminate where the symbol started.  */
	      *name = 0;
	      if (forced)
		{
		  if (c == '(')
		    {
		      /* Subscripted substitution symbol -- use just the
			 indicated portion of the string; the description
			 kinda indicates that forced substitution is not
			 supposed to be recursive, but I'm not sure.  */

		      /* Default to a single char.  */
		      unsigned beg, len = 1;
		      char *newval = strcpy (xmalloc (strlen (value) + 1), value);

		      savedp = input_line_pointer;
		      input_line_pointer = tail + 1;
		      beg = get_absolute_expression ();
		      if (beg < 1)
			{
			  as_bad (_("Invalid subscript (use 1 to %d)"),
				  (int) strlen (value));
			  break;
			}
		      if (*input_line_pointer == ',')
			{
			  ++input_line_pointer;
			  len = get_absolute_expression ();
			  if (beg + len > strlen (value))
			    {
			      as_bad (_("Invalid length (use 0 to %d"),
				      (int) (strlen (value) - beg));
			      break;
			    }
			}
		      newval += beg - 1;
		      newval[len] = 0;
		      tail = input_line_pointer;
		      if (*tail++ != ')')
			{
			  as_bad (_("Missing ')' in subscripted substitution symbol expression"));
			  break;
			}
		      c = *tail;
		      input_line_pointer = savedp;

		      value = newval;
		    }
		  name[-1] = 0;
		}
	      tmp = xmalloc (strlen (head) + strlen (value) + strlen (tail + 1)
			     + 2);
	      strcpy (tmp, head);
	      strcat (tmp, value);
	      /* Make sure forced substitutions are properly terminated.  */
	      if (forced)
		{
		  if (c != ':')
		    {
		      as_bad (_("Missing forced substitution terminator ':'"));
		      break;
		    }
		  ++tail;
		}
	      else
		*tail = c;	/* Restore the character after the symbol end.  */
	      strcat (tmp, tail);
	      /* Continue examining after the replacement value.  */
	      ptr = tmp + strlen (head) + strlen (value);
	      free (replacement);
	      head = replacement = tmp;
	      changed = 1;
	    }
	  else
	    *ptr = c;
	}
      else
	{
	  /* Need to take care of [reg-offset] issue.  */
	  if (ptr[0] == '[')
	    inRI5 = 1;
	  else if (inRI5)
	    {
	      if (ptr[0] == '-')
		{
		  char *fstr, *tstr;

		  if (ISDIGIT (ptr[1]) || ptr[1] == '(')
		    {
		      /* "[reg-offset]" --> "[reg+(-offset)]"  */
		      tstr = ptr + strlen (ptr);
		      fstr = strchr (ptr, ']');

		      for (; tstr >= fstr; tstr--)
			tstr[3] = tstr[0];
		      tstr[3] = ')';
		      for (fstr--; fstr >= ptr; fstr--)
			fstr[2] = fstr[0];
		      ptr[0] = '+';
		      ptr[1] = '(';
		      changed = 1;
		    }
		  else if (ptr[1] == '-')
		    {
		      /* "[reg--offset]" --> "[reg+offset]"  */
		      fstr = ptr++;
		      for (*fstr++ = '+'; fstr[1] != '\0'; fstr++)
			fstr[0] = fstr[1];
		      *fstr = fstr[1];
		      fstr++;
		      *fstr = '\0';
		      changed = 1;
		    }
		  else if (ptr[1] == '+')
		    {
		      /* "[reg-+offset]" --> "[reg+(-offset)]"  */
		      tstr = ptr + strlen (ptr);
		      fstr = strchr (ptr, ']');

		      for (; tstr >= fstr; tstr--)
			tstr[2] = tstr[0];
		      tstr[2] = ')';
		      for (fstr--; fstr > ptr; fstr--)
			fstr[1] = fstr[0];
		      ptr[0] = '+';
		      ptr[1] = '(';
		      ptr[2] = '-';
		      changed = 1;
		    }
		}
	      inRI5 = 0;
	    }
	  ++ptr;
	}
    }

  if (changed)
    return replacement;
  else
    {
      /* No changes.  Free work copy first.  */
      free (replacement);
      return line;
    }
}

/* This function returns the length of symbol A.  */

static int
builtin_strlen (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  return strlen (a);
}

/* This function compares symbol A to string B.  */

static int
builtin_strcmp (char *a, char *b)
{
  return strcmp (a, b);
}

/* This function compares symbol A to string B ignoring case.  */

static int
builtin_strcasecmp (char *a, char *b)
{
  return strcasecmp (a, b);
}

/* This function checks whether char B is found in string A.  */

static int
builtin_strchr (char *a, char *b)
{
  return strchr (a, *b) != NULL;
}

/* This function checks whether string B is found in string A.  */

static int
builtin_strstr (char *a, char *b)
{
  return strstr (a, b) != NULL;
}

/* This function checks whether string B is found in string A ignoring case.  */

static int
builtin_strcasestr (char *a, char *b)
{
  return nds32_strcasestr (a, b) != NULL;
}

/* This function returns the index of the first occurrence of B in A, or zero
   if none assumes B is an integer char value as a string.  Index is one-based.  */

static int
builtin_firstch (char *a, char *b)
{
  int val = atoi (b);
  char *tmp = strchr (a, val);

  return tmp ? tmp - a + 1 : 0;
}

/* This function returns index of last occurrence of B in A.  */

static int
builtin_lastch (char *a, char *b)
{
  int val = atoi (b);
  char *tmp = strrchr (a, val);

  return tmp ? tmp - a + 1 : 0;
}

/* This function returns 1 if string A is defined in the symbol table
   (NOT the substitution symbol table).  */

static int
builtin_isdefed (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  symbolS *symbolP = symbol_find (a);

  return symbolP != NULL;
}

/* This function assigns first member of comma-separated list B (e.g. "1,2,3")
   to the symbol A, or zero if B is a null string.  Both arguments *must* be
   substitution symbols, unsubstituted.  */

static int
builtin_ismember (char *sym, char *list)
{
  char *elem, *ptr, *listv;

  if (!list)
    return 0;

  listv = builtin_lookup (list, macro_level);
  if (!listv)
    {
      as_bad (_("Undefined substitution symbol '%s'"), list);
      ignore_rest_of_line ();
      return 0;
    }

  ptr = elem = xmalloc (strlen (listv) + 1);
  strcpy (elem, listv);
  while (*ptr && *ptr != ',')
    ++ptr;
  *ptr++ = 0;

  builtin_create_or_replace (sym, elem);

  /* Reassign the list.  */
  builtin_create_or_replace (list, ptr);

  /* Assume this value, docs aren't clear.  */
  return *list != 0;
}

/* This function reads an expression from a C string and returns a pointer past
   the end of the expression.  */

static char *
parse_expression (char *str, expressionS *exp)
{
  char *s;
  char *tmp;

  tmp = input_line_pointer;	/* Save line pointer.  */
  input_line_pointer = str;
  expression (exp);
  s = input_line_pointer;
  input_line_pointer = tmp;	/* Restore line pointer.  */

  return s;			/* Return pointer to where parsing stopped.  */
}

/* This function returns zero if not a constant; otherwise:
   1 if binary
   2 if octal
   3 if hexadecimal
   4 if character
   5 if decimal.  */

static int
builtin_iscons (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  expressionS exp;

  parse_expression (a, &exp);

  if (exp.X_op == O_constant)
    {
      int len = strlen (a);

      /*  No suffix; either octal, hex, or decimal.  */
      if (*a == '0' && len > 1)
	{
	  if (TOUPPER (a[1]) == 'B')
	    return 1;
	  else if (TOUPPER (a[1]) == 'X')
	    return 3;
	  else
	    return 2;
	}

      return 5;
    }

  return 0;
}

/* This function returns 1 if given argument is an odd integer and 0 otherwise.  */

static int
builtin_isodd (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  expressionS exp;

  parse_expression (a, &exp);

  if (exp.X_op == O_constant)
    return exp.X_add_number % 2;
  else
    return 0;
}

/* This function returns 1 if A is a valid symbol name.  */

static int
builtin_isname (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  if (!is_name_beginner (*a))
    return 0;
  while (*a)
    {
      if (!is_part_of_name (*a))
	return 0;
      ++a;
    }

  return 1;
}

/* This function returns whether the string is a 5-bit addressable register.  */

static int
builtin_isreg5 (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  if (hash_find (reg5_hash, a))
    return 1;

  return 0;
}

/* This function returns whether the string is an RI expression
   - an expression of register +/- immediate.  */

static int
builtin_isRI5 (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  char *pstr = strpbrk (a, "+-");

  if (pstr == NULL)
    return builtin_isreg5 (a, ignore);
  else
    {
      char ch = *pstr;

      /* R+I?  */
      *pstr = '\0';
      if (hash_find (reg5_hash, a))
	{
	  *pstr = ch;
	  return builtin_iscons (pstr + 1, ignore);
	}

      return 0;
    }
}

/* This function returns whether the string is a 4-bit addressed register.  */

static int
builtin_isreg4 (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  if (hash_find (reg4_hash, a))
    return 1;

  return 0;
}

/* This function returns whether the string is a 3-bit addressed register.  */

static int
builtin_isreg3 (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  if (hash_find (reg3_hash, a))
    return 1;

  return 0;
}

/* This function returns whether the string is a register.  */

static int
builtin_isreg (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  if (hash_find (reg5_hash, a)
      || hash_find (reg4_hash, a) || hash_find (reg3_hash, a))
    return 1;

  return 0;
}

/* This function returns the register number of the given GPR.  */

static int
builtin_regnum (char *a, char *ignore ATTRIBUTE_UNUSED)
{
  nds32_regs *sym;

  if ((sym = (nds32_regs *) hash_find (reg5_hash, a))
      || (sym = (nds32_regs *) hash_find (reg4_hash, a))
      || (sym = (nds32_regs *) hash_find (reg3_hash, a)))
    return sym->index;
  else
    return -1;
}

/* This function returns the register number of the given GPR.  */

static int
builtin_mask4bit (char *a, char *b)
{
  nds32_regs *sym1 = (nds32_regs *) hash_find (reg5_hash, a);
  nds32_regs *sym2 = (nds32_regs *) hash_find (reg5_hash, b);

  if (sym1 == NULL || sym2 == NULL || sym1->index < 28 || sym2->index < 28)
    return -1;
  else
    {
      int i, j, k;

      for (i = sym1->index, j = 8 >> (sym1->index - 28), k = 0;
	   i <= sym2->index; i++)
	{
	  k |= j;
	  j >>= 1;
	}

      return k;
    }
}


/* This function returns the pic_code flag.  */

static int
builtin_genpic (char *a ATTRIBUTE_UNUSED, char *ignore ATTRIBUTE_UNUSED)
{
  return pic_code;
}

/* Extract addend after symbol.
   FIXME: Remove this.  */

static int
builtin_addend (const char *sym, char *ignore ATTRIBUTE_UNUSED)
{
  while (*sym != '+' && *sym != '-' && *sym)
    ++sym;

  if (*sym == 0)
    return 0;
  else
    return strtol (sym, NULL, 0);
}

/* Assembler built-in string substitution functions.  */
static const builtin_proc_entry builtin_procs[] = {
  {"$strlen", builtin_strlen, 1},
  {"$strcmp", builtin_strcmp, 2},
  {"$strcasecmp", builtin_strcasecmp, 2},
  {"$strchr", builtin_strchr, 2},
  {"$strstr", builtin_strstr, 2},
  {"$strcasestr", builtin_strcasestr, 2},
  {"$firstch", builtin_firstch, 2},
  {"$lastch", builtin_lastch, 2},
  {"$isdefed", builtin_isdefed, 1},
  {"$ismember", builtin_ismember, 2},
  {"$iscons", builtin_iscons, 1},
  {"$isodd", builtin_isodd, 1},
  {"$isname", builtin_isname, 1},
  {"$isreg5", builtin_isreg5, 1},
  {"$isRI5", builtin_isRI5, 1},
  {"$isreg4", builtin_isreg4, 1},
  {"$isreg3", builtin_isreg3, 1},
  {"$isreg", builtin_isreg, 1},
  {"$regnum", builtin_regnum, 1},
  {"$mask4bit", builtin_mask4bit, 2},
  {"$genpic", builtin_genpic, 0},
  {NULL, NULL, 0}
};

/*
 * Pseudo opcodes
 */

typedef void (*nds32_pseudo_opcode_func) (int argc, char *argv[], int pv);
struct nds32_pseudo_opcode
{
  const char *opcode;
  int argc;
  nds32_pseudo_opcode_func proc;
  int pseudo_val;

  /* Some instructions are not pseudo opcode, but they might sill be expanded or changed
     with other instruction combination for some conditions.
     We also apply this structure to assist such work.

     For example, if the distance of branch target '.L0' is larger than imm8s<<1 range,

     the instruction:

         beqzs8 .L0

     will be transformed into:

         bnezs8  .LCB0
         j  .L0
       .LCB0:

     However, sometimes we do not want assembler to do such changes
     because compiler knows how to generate corresponding instruction sequence.
     Use this field to indicate that this opcode is also a physical instruction.
     If the flag 'compiler_generated_asm' is nozero and this opcode
     is a physical instruction, we should not expand it.  */
  int physical_op;
};
#define PV_DONT_CARE 0

static struct hash_control *nds32_pseudo_opcode_hash = NULL;

static void
md_assemblef (char *format, ...)
{
  char line[1024]; /* FIXME: hope this is long enough.  */
  va_list ap;

  va_start (ap, format);
  vsnprintf (line, sizeof (line), format, ap);
  md_assemble (line);
}

static void
as_bad_no16 (void)
{
  as_bad (_("option specified no 16-bit instructions."));
}

/* Some prototypes here, since some op may use another op.  */
static void do_pseudo_li_internal (char *rt, int imm32s);
static void do_pseudo_move_reg_internal (char *dst, char *src);
static void do_pseudo_jral (int argc, char *argv[], int pv);

static void
do_pseudo_b (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  char *arg_label = argv[0];
  /* b   label */
  if (pic_code
      && (strstr (arg_label, "@GOT") || strstr (arg_label, "@PLT")))
    {
      md_assemblef ("sethi $ta,hi20(%s)", arg_label);
      md_assemblef ("ori $ta,$ta,lo12(%s)", arg_label);
      md_assemble  ("add $ta,$ta,$gp");
      md_assemblef ("jr $ta");
    }
  else
    {
      if (disable_16bit)
	md_assemblef ("j_r %s", arg_label);
      else
	md_assemblef ("j8_r %s", arg_label);
    }
}

static void
do_pseudo_bal (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  char *arg_label = argv[0];
  /* bal|call  label */
  if (pic_code
      && (strstr (arg_label, "@GOT") || strstr (arg_label, "@PLT")))
    {
      md_assemblef ("sethi $ta,hi20(%s)", arg_label);
      md_assemblef ("ori $ta,$ta,lo12(%s)", arg_label);
      md_assemble  ("add $ta,$ta,$gp");
      md_assemblef ("jral $ta");
    }
  else
    {
      md_assemblef ("jal_r %s", arg_label);
    }
}

static void
do_pseudo_beq (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* beq rt5, ra5, label */
  /* TODO check rt5 == ra5 */
  md_assemblef ("beq_r %s,%s,%s", argv[0], argv[1], argv[2]);
}

static void
do_pseudo_beqs38 (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* beqs38 rt3, label */
  /* TODO check rt3 == R5 */
  if (disable_16bit)
    as_bad_no16 ();
  md_assemblef ("beqs38_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_beqz (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  md_assemblef ("beqz_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_beqz38 (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  if (disable_16bit)
    as_bad_no16 ();
  md_assemblef ("beqz38_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_beqzs8 (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  if (disable_16bit)
    as_bad_no16 ();
  md_assemblef ("beqzs8_r %s", argv[0]);
}

static void
do_pseudo_bge (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, ra5, label */
  if (!disable_16bit && builtin_isreg4 (argv[0], NULL))
    {
      md_assemblef ("slt45 %s,%s", argv[0], argv[1]);
      md_assemblef ("beqzs8_r %s", argv[2]);
    }
  else
    {
      md_assemblef ("slt $ta,%s,%s", argv[0], argv[1]);
      md_assemblef ("beqz_r $ta,%s", argv[2]);
    }
}

static void
do_pseudo_bges (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, ra5, label */
  if (!disable_16bit && builtin_isreg4 (argv[0], NULL))
    {
      md_assemblef ("slts45 %s,%s", argv[0], argv[1]);
      md_assemblef ("beqzs8_r %s", argv[2]);
    }
  else
    {
      md_assemblef ("slts $ta,%s,%s", argv[0], argv[1]);
      md_assemblef ("beqz_r $ta,%s", argv[2]);
    }
}

static void
do_pseudo_bgez (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, label */
  md_assemblef ("bgez_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_bgezal (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, label */
  md_assemblef ("bgezal_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_bgt (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* bgt rt5, ra5, label */
  if (!disable_16bit && builtin_isreg4 (argv[1], NULL))
    {
      md_assemblef ("slt45 %s,%s", argv[1], argv[0]);
      md_assemblef ("bnezs8_r %s", argv[2]);
    }
  else
    {
      md_assemblef ("slt $ta,%s,%s", argv[1], argv[0]);
      md_assemblef ("bnez_r $ta,%s", argv[2]);
    }
}

static void
do_pseudo_bgts (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* bgt rt5, ra5, label */
  if (!disable_16bit && builtin_isreg4 (argv[1], NULL))
    {
      md_assemblef ("slts45 %s,%s", argv[1], argv[0]);
      md_assemblef ("bnezs8_r %s", argv[2]);
    }
  else
    {
      md_assemblef ("slts $ta,%s,%s", argv[1], argv[0]);
      md_assemblef ("bnez_r $ta,%s", argv[2]);
    }
}

static void
do_pseudo_bgtz (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* bgtz rt5, label */
  md_assemblef ("bgtz_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_ble (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* bgt rt5, ra5, label */
  if (!disable_16bit && builtin_isreg4 (argv[1], NULL))
    {
      md_assemblef ("slt45 %s,%s", argv[1], argv[0]);
      md_assemblef ("beqzs8_r %s", argv[2]);
    }
  else
    {
      md_assemblef ("slt $ta,%s,%s", argv[1], argv[0]);
      md_assemblef ("beqz_r $ta,%s", argv[2]);
    }
}

static void
do_pseudo_bles (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* bgt rt5, ra5, label */
  if (!disable_16bit && builtin_isreg4 (argv[1], NULL))
    {
      md_assemblef ("slts45 %s,%s", argv[1], argv[0]);
      md_assemblef ("beqzs8_r %s", argv[2]);
    }
  else
    {
      md_assemblef ("slts $ta,%s,%s", argv[1], argv[0]);
      md_assemblef ("beqz_r $ta,%s", argv[2]);
    }
}

static void
do_pseudo_blez (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* bgtz rt5, label */
  md_assemblef ("blez_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_blt (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, ra5, label */
  if (!disable_16bit && builtin_isreg4 (argv[0], NULL))
    {
      md_assemblef ("slt45 %s,%s", argv[0], argv[1]);
      md_assemblef ("bnezs8_r %s", argv[2]);
    }
  else
    {
      md_assemblef ("slt $ta,%s,%s", argv[0], argv[1]);
      md_assemblef ("bnez_r $ta,%s", argv[2]);
    }
}

static void
do_pseudo_blts (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, ra5, label */
  if (!disable_16bit && builtin_isreg4 (argv[0], NULL))
    {
      md_assemblef ("slts45 %s,%s", argv[0], argv[1]);
      md_assemblef ("bnezs8_r %s", argv[2]);
    }
  else
    {
      md_assemblef ("slts $ta,%s,%s", argv[0], argv[1]);
      md_assemblef ("bnez_r $ta,%s", argv[2]);
    }
}

static void
do_pseudo_bltz (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, label */
  md_assemblef ("bltz_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_bltzal (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, label */
  md_assemblef ("bltzal_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_bne (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt5, label */
  /* TODO check argv[0] == argv[1] for always take */
  md_assemblef ("bne_r %s,%s,%s", argv[0], argv[1], argv[2]);
}

static void
do_pseudo_bnes38 (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* rt3, label */
  if (disable_16bit)
    as_bad_no16 ();
  /* TODO: check r3, check rt3 == $r3 */
  md_assemblef ("bnes38_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_bnez (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  md_assemblef ("bnez_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_bnez38 (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  if (disable_16bit)
    as_bad_no16 ();
  md_assemblef ("bnez38_r %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_bnezs8 (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  if (disable_16bit)
    as_bad_no16 ();
  md_assemblef ("bnezs8_r %s", argv[0]);
}

static void
do_pseudo_br (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  if (disable_16bit)
    md_assemblef ("jr %s", argv[0]);
  else
    md_assemblef ("jr5 %s", argv[0]);
}

static void
do_pseudo_bral (int argc, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  if (argc != 1)
    as_bad ("unrecognized form of instruction. %s", argv[argc]);

  if (!disable_16bit && relax_jal_bound > 0
      && (multi_call_relax || pltgot_call_relax))
    md_assemblef ("jral_r $lp,%s", argv[0]);
  else
    do_pseudo_jral (argc, argv, PV_DONT_CARE);
}

static void
do_pseudo_jral (int argc, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* jral    rt=lp, rb */
  /* jral5   rb5 */
  /* If there are only argc, it must be jral5 rb5 (rt==lp).  */
  int rt = 30, rb;

  if (argc == 1)
    rb =  builtin_regnum (argv[0], NULL);
  else if (argc == 2)
    {
      rt =  builtin_regnum (argv[0], NULL);
      rb =  builtin_regnum (argv[1], NULL);
    }
  else
    {
      as_bad ("Unexpected number of arguments of jral. %s", argv[argc]);
      return;
    }

  if (!disable_16bit && rt == 30)
    md_assemblef ("jral5_r $r%d", rb);
  else
    md_assemblef ("jral_r $r%d,$r%d", rt, rb);
}

static void
do_pseudo_la_internal (const char *arg_reg, const char *arg_label, const char *line)
{
  /* rt, label */
  if (!pic_code)
    {
      md_assemblef ("sethi %s,hi20(%s)", arg_reg, arg_label);
      md_assemblef ("ori %s,%s,lo12(%s)", arg_reg, arg_reg, arg_label);
    }
  else if ((strstr (arg_label, "@PLT") || strstr (arg_label, "@GOTOFF")))
    {
      md_assemblef ("sethi $ta,hi20(%s)", arg_label);
      md_assemblef ("ori $ta,$ta,lo12(%s)", arg_label);
      md_assemblef ("add %s,$ta,$gp", arg_reg);
    }
  else if (strstr (arg_label, "@GOT"))
    {
      long addend = builtin_addend (arg_label, NULL);

      md_assemblef ("sethi $ta,hi20(%s)", arg_label);
      md_assemblef ("ori $ta,$ta,lo12(%s)", arg_label);
      md_assemblef ("lw %s,[$gp+$ta]", arg_reg);
      if (addend != 0)
	{
	  if (addend < 0x4000 && addend >= -0x4000)
	    {
	      md_assemblef ("addi %s,%s,%d", arg_reg, arg_reg, addend);
	    }
	  else
	    {
	      do_pseudo_li_internal ("$ta", addend);
	      md_assemblef ("add %s,$ta,%s", arg_reg, arg_reg);
	    }
	}
    }
   else
      as_bad (_("need PIC qualifier with symbol. '%s'"), line);
}

static void
do_pseudo_la (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  do_pseudo_la_internal (argv[0], argv[1], argv[argc]);
}

static void
do_pseudo_li_internal (char *rt, int imm32s)
{
  if (!disable_16bit && imm32s <= 0xf && imm32s >= -0x10)
    md_assemblef ("movi55 %s,lo20(%d)", rt, imm32s);
  else if (imm32s <= 0x7ffff && imm32s >= -0x80000)
    md_assemblef ("movi %s,lo20(%d)", rt, imm32s);
  else if ((imm32s & 0xfff) == 0)
    md_assemblef ("sethi %s,hi20(%d)", rt, imm32s);
  else
    {
      md_assemblef ("sethi %s,hi20(%d)", rt, imm32s);
      md_assemblef ("ori %s,%s,lo12(%d)", rt, rt, imm32s);
    }
}

static void
do_pseudo_li (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* Validate argv[1] for constant expression.  */
  expressionS exp;

  parse_expression (argv[1], &exp);
  if (exp.X_op != O_constant)
    {
      as_bad (_("Operand is not a constant. `%s'"), argv[argc]);
      return;
    }

  do_pseudo_li_internal (argv[0], exp.X_add_number);
}

static void
do_pseudo_ls_bhw (int argc ATTRIBUTE_UNUSED, char *argv[], int pv)
{
  char ls = 'r';
  char size = 'x';
  const char *sign = "";

  /* Prepare arguments for various load/store.  */
  sign = (pv & 0x10) ? "s" : "";
  ls = (pv & 0x80000000) ? 's' : 'l';
  switch (pv & 0x3)
    {
    case 0: size = 'b'; break;
    case 1: size = 'h'; break;
    case 2: size = 'w'; break;
    }

  if (ls == 's' || size == 'w')
    sign = "";

  if (builtin_isreg (argv[1], NULL))
    {
      /* lwi */
      md_assemblef ("%c%c%si %s,[%s]", ls, size, argv[0], argv[1]);
    }
  else if (!pic_code)
    {
      /* lwi */
      md_assemblef ("sethi $ta,hi20(%s)", argv[1]);
      md_assemblef ("%c%c%si %s,[$ta+lo12(%s)]", ls, size, sign, argv[0], argv[1]);
    }
  else
    {
      /* PIC code.  */
      if (strstr (argv[1], "@GOTOFF"))
	{
	  /* lw */
	  md_assemblef ("sethi $ta,hi20(%s)", argv[1]);
	  md_assemblef ("ori $ta,$ta,lo12(%s)", argv[1]);
	  md_assemblef ("%c%c%s %s,[$ta+$gp]", ls, size, sign, argv[0]);
	}
      else if (strstr (argv[1], "@GOT"))
	{
	  long addend = builtin_addend (argv[1], NULL);
	  /* lw */
	  md_assemblef ("sethi $ta,hi20(%s)", argv[1]);
	  md_assemblef ("ori $ta,$ta,lo12(%s)", argv[1]);
	  md_assemblef ("lw $ta,[$gp+$ta]");	/* Load address word.  */
	  if (addend < 0x10000 && addend >= -0x10000)
	    {
	      md_assemblef ("%c%c%si %s,[$ta+(%d)]", ls, size, sign, argv[0], addend);
	    }
	  else
	    {
	      /* lw */
	      do_pseudo_li_internal (argv[0], addend);
	      md_assemblef ("%c%c%s %s,[$ta+%s]", ls, size, sign, argv[0], argv[0]);
	    }
	}
      else
	{
	  as_bad (_("needs @GOT or @GOTOFF. %s"), argv[argc]);
	}
    }
}

static void
do_pseudo_ls_bhwp (int argc ATTRIBUTE_UNUSED, char *argv[], int pv)
{
  char *arg_rt = argv[0];
  char *arg_label = argv[1];
  char *arg_inc = argv[2];
  char ls = 'r';
  char size = 'x';
  const char *sign = "";

  /* Prepare arguments for various load/store.  */
  sign = (pv & 0x10) ? "s" : "";
  ls = (pv & 0x80000000) ? 's' : 'l';
  switch (pv & 0x3)
    {
    case 0: size = 'b'; break;
    case 1: size = 'h'; break;
    case 2: size = 'w'; break;
    }

  if (ls == 's' || size == 'w')
    sign = "";

  do_pseudo_la_internal ("$ta", arg_label, argv[argc]);
  md_assemblef ("%c%c%si.bi %s,[$ta],%s", ls, size, sign,
	arg_rt, arg_inc);
}

static void
do_pseudo_move_reg_internal (char *dst, char *src)
{
  if (disable_16bit)
    md_assemblef ("ori %s,%s,0", dst, src);
  else
    md_assemblef ("mov55 %s,%s", dst, src);
}

static void
do_pseudo_move (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  if (builtin_isreg (argv[1], NULL))
    do_pseudo_move_reg_internal (argv[0], argv[1]);
  else if (builtin_iscons (argv[1], NULL))
    /* move $rt, imm  -> li $rt, imm */
    do_pseudo_li (argc, argv, PV_DONT_CARE);
  else
    /* move $rt, label  -> l.w $rt, label */
    do_pseudo_ls_bhw (argc, argv, 2); /* for load word */
}

static void
do_pseudo_neg (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  md_assemble ("movi $ta,0");
  md_assemblef ("sub %s,$ta,%s", argv[0], argv[1]);
}

static void
do_pseudo_not (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  md_assemblef ("nor %s,%s,%s", argv[0], argv[1], argv[1]);
}

static void
do_pseudo_pushpopm (int argc, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* posh/pop $ra, $rb */
  /* SMW.{b | a}{i | d}{m?} Rb, [Ra], Re, Enable4 */
  int rb, re, ra, en4;
  int i;
  char *opc = "pushpopm";

  if (argc == 3)
    as_bad ("'pushm/popm $ra5, $rb5, $label' is deprecated.  "
	    "Only 'pushm/popm $ra5' is supported now. %s", argv[argc]);
  else if (argc == 1)
    as_bad ("'pushm/popm $ra5, $rb5'. %s\n", argv[argc]);

  if (strstr (argv[argc], "pop") == argv[argc])
    opc = "lmw.bim";
  else if (strstr (argv[argc], "push") == argv[argc])
    opc = "smw.adm";
  else
    as_fatal ("nds32-as internal error. %s", argv[argc]);

  rb = builtin_regnum (argv[0], NULL);
  re = builtin_regnum (argv[1], NULL);

  if (re < rb)
    {
      as_warn ("$rb should not be smaller than $ra. %s", argv[argc]);
      /* Swap to right order.  */
      ra = re;
      re = rb;
      rb = ra;
    }

  /* Build enable4 mask.  */
  en4 = 0;
  if (re >= 28 || rb >= 28)
    {
      for (i = (rb >= 28? rb: 28); i <= re; i++)
	en4 |= 1 << (3 - (i - 28));
    }

  /* Adjust $re, $rb.  */
  if (rb >= 28)
    rb = re = 31;
  else if (re >= 28)
    re = 27;

  md_assemblef ("%s $r%d,[$sp],$r%d,%d", opc, rb, re, en4);
}

static void
do_pseudo_pushpop (int argc, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  /* push/pop $ra5, $label=$sp */
  char *argvm[3];

  if (argc == 2)
    as_bad ("'push/pop $ra5, rb5' is deprecated.  "
	    "Only 'push/pop $ra5' is supported now. %s", argv[argc]);

  argvm[0] = argv[0];
  argvm[1] = argv[0];
  argvm[2] = argv[argc];
  do_pseudo_pushpopm (2, argvm, PV_DONT_CARE);
#if 0
  if (strstr (argv[argc], "pop ") == argv[argc])
    opc = "lmw.bim";
  else if (strstr (argv[argc], "push ") == argv[argc])
    opc = "smw.adm";
  else
    as_fatal ("nds32-as internal error. %s", argv[argc]);

  ra5 = builtin_regnum (argv[0], NULL);
  if (ra5 >= 28)
    {
      int mask = 1 << (3 - (ra5 - 28));
      md_assemblef ("%s $sp,[$sp],$sp,%d", opc, mask);
    }
  else
    {
      md_assemblef ("%s %s,[$sp],%s", opc, argv[0], argv[0]);
    }
#endif
}

static void
do_pseudo_v3push (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  md_assemblef ("push25 %s,%s", argv[0], argv[1]);
}

static void
do_pseudo_v3pop (int argc ATTRIBUTE_UNUSED, char *argv[], int pv ATTRIBUTE_UNUSED)
{
  md_assemblef ("pop25 %s,%s", argv[0], argv[1]);
}

/* pv == 0, parsing "push.s" pseudo instruction operands.
   pv != 0, parsing "pop.s" pseudo instruction operands.  */

static void
do_pseudo_pushpop_stack (int argc, char *argv[], int pv)
{
  /* push.s Rb,Re,{$fp $gp $lp $sp}  ==>  smw.adm Rb,[$sp],Re,Eable4  */
  /* pop.s Rb,Re,{$fp $gp $lp $sp}   ==>  lmw.bim Rb,[$sp],Re,Eable4  */

  int rb, re;
  int en4;
  int last_arg_index;
  char *opc = (pv == 0) ? "smw.adm" : "lmw.bim";

  rb = re = 0;

  if (argc == 1)
    {
      /* argc=1, operands pattern: { $fp $gp $lp $sp }  */

      /* Set register number Rb = Re = $sp = $r31.  */
      rb = re = 31;
    }
  else if (argc == 2 || argc == 3)
    {
      /* argc=2, operands pattern: Rb, Re  */
      /* argc=3, operands pattern: Rb, Re, { $fp $gp $lp $sp }  */

      /* Get register number in integer.  */
      rb = builtin_regnum (argv[0], NULL);
      re = builtin_regnum (argv[1], NULL);

      /* Rb should be equal/less than Re.  */
      if (rb > re)
	as_bad ("The first operand (%s) should be equal to or smaller than second operand (%s).", argv[0], argv[1]);

      /* forbid using $fp|$gp|$lp|$sp in Rb or Re
		      r28 r29 r30 r31  */
      if (rb >= 28)
	as_bad ("Cannot use $fp, $gp, $lp, or $sp at first operand !!");
      if (re >= 28)
	as_bad ("Cannot use $fp, $gp, $lp, or $sp at second operand !!");
    }
  else
    {
      as_bad ("Invalid operands pattern !!");
    }

  /* Build Enable4 mask.  */
  /* Using last_arg_index for argc=1|2|3 is safe, because $fp, $gp, $lp,
     and $sp only appear in argc=1 or argc=3 if argc=2, en4 remains 0,
     which is also valid for code generation.  */
  en4 = 0;
  last_arg_index = argc - 1;
  if (strstr (argv[last_arg_index], "$fp"))
    en4 |= 8;
  if (strstr (argv[last_arg_index], "$gp"))
    en4 |= 4;
  if (strstr (argv[last_arg_index], "$lp"))
    en4 |= 2;
  if (strstr (argv[last_arg_index], "$sp"))
    en4 |= 1;

  md_assemblef ("%s $r%d,[$sp],$r%d,%d", opc, rb, re, en4);
}


/* TODO: validate arguments */
struct nds32_pseudo_opcode nds32_pseudo_opcode_table[] = {
  {"b",      1, do_pseudo_b,      0, 0},
  {"bal",    1, do_pseudo_bal,    0, 0},

  {"beq",    3, do_pseudo_beq,    0, 1},
  {"beqs38", 2, do_pseudo_beqs38, 0, 1},
  {"beqz",   2, do_pseudo_beqz,   0, 1},
  {"beqz38", 2, do_pseudo_beqz38, 0, 1},
  {"beqzs8", 1, do_pseudo_beqzs8, 0, 1},

  {"bge",    3, do_pseudo_bge,    0, 0},
  {"bges",   3, do_pseudo_bges,   0, 0},
  {"bgez",   2, do_pseudo_bgez,   0, 1},
  {"bgezal", 2, do_pseudo_bgezal, 0, 1},

  {"bgt",    3, do_pseudo_bgt,    0, 0},
  {"bgts",   3, do_pseudo_bgts,   0, 0},
  {"bgtz",   2, do_pseudo_bgtz,   0, 1},

  {"ble",    3, do_pseudo_ble,    0, 0},
  {"bles",   3, do_pseudo_bles,   0, 0},
  {"blez",   2, do_pseudo_blez,   0, 1},

  {"blt",    3, do_pseudo_blt,    0, 0},
  {"blts",   3, do_pseudo_blts,   0, 0},
  {"bltz",   2, do_pseudo_bltz,   0, 1},
  {"bltzal", 2, do_pseudo_bltzal, 0, 1},

  {"bne",    3, do_pseudo_bne,    0, 1},
  {"bnes38", 2, do_pseudo_bnes38, 0, 1},
  {"bnez",   2, do_pseudo_bnez,   0, 1},
  {"bnez38", 2, do_pseudo_bnez38, 0, 1},
  {"bnezs8", 1, do_pseudo_bnezs8, 0, 1},

  {"br",     1, do_pseudo_br,     0, 0},
  {"bral",   1, do_pseudo_bral,   0, 0},

  {"call",   1, do_pseudo_bal,    0, 0},
  {"jral5",  1, do_pseudo_jral,   0, 1},

  {"la",     2, do_pseudo_la, 0, 0},
  {"li",     2, do_pseudo_li, 0, 0},

  {"l.b",    2, do_pseudo_ls_bhw, 0, 0},
  {"l.h",    2, do_pseudo_ls_bhw, 1, 0},
  {"l.w",    2, do_pseudo_ls_bhw, 2, 0},
  {"l.bs",   2, do_pseudo_ls_bhw, 0 | 0x10, 0},
  {"l.hs",   2, do_pseudo_ls_bhw, 1 | 0x10, 0},
  {"s.b",    2, do_pseudo_ls_bhw, 0 | 0x80000000, 0},
  {"s.h",    2, do_pseudo_ls_bhw, 1 | 0x80000000, 0},
  {"s.w",    2, do_pseudo_ls_bhw, 2 | 0x80000000, 0},

  {"l.bp",   3, do_pseudo_ls_bhwp, 0, 0},
  {"l.hp",   3, do_pseudo_ls_bhwp, 1, 0},
  {"l.wp",   3, do_pseudo_ls_bhwp, 2, 0},
  {"l.bsp",  3, do_pseudo_ls_bhwp, 0 | 0x10, 0},
  {"l.hsp",  3, do_pseudo_ls_bhwp, 1 | 0x10, 0},
  {"s.bp",   3, do_pseudo_ls_bhwp, 0 | 0x80000000, 0},
  {"s.hp",   3, do_pseudo_ls_bhwp, 1 | 0x80000000, 0},
  {"s.wp",   3, do_pseudo_ls_bhwp, 2 | 0x80000000, 0},
  {"s.bsp",  3, do_pseudo_ls_bhwp, 0 | 0x80000000 | 0x10, 0},
  {"s.hsp",  3, do_pseudo_ls_bhwp, 1 | 0x80000000 | 0x10, 0},

#if 0
  {"lb.p", },
  {"lh.p", },
  {"lw.p", },
  {"lbi.p", },
  {"lhi.p", },
  {"lwi.p", },
  {"lbsi.p", },
  {"lhsi.p", },
  {"lbs.p", },
  {"lhs.p", },
#endif


  {"move",   2, do_pseudo_move, 0, 0},
  {"neg",    2, do_pseudo_neg,  0, 0},
  {"not",    2, do_pseudo_not,  0, 0},

  {"pop",    2, do_pseudo_pushpop,   0, 0},
  {"push",   2, do_pseudo_pushpop,   0, 0},
  {"popm",   2, do_pseudo_pushpopm,  0, 0},
  {"pushm",   3, do_pseudo_pushpopm, 0, 0},

  {"v3push", 2, do_pseudo_v3push, 0, 0},
  {"v3pop",  2, do_pseudo_v3pop,  0, 0},

  /* jasonwu:
       Support pseudo instructions of pushing/poping registers into/from stack
	push.s  Rb, Re, { $fp $gp $lp $sp }  ==>  smw.adm  Rb,[$sp],Re,Enable4
	pop.s   Rb, Re, { $fp $gp $lp $sp }  ==>  lmw.bim  Rb,[$sp],Re,Enable4
   */
  { "push.s", 3, do_pseudo_pushpop_stack, 0, 0 },
  { "pop.s", 3, do_pseudo_pushpop_stack, 1, 0 },

  {NULL, 0, NULL, 0, 0}
};

static void
nds32_init_nds32_pseudo_opcodes (void)
{
  struct nds32_pseudo_opcode *opcode = nds32_pseudo_opcode_table;
  nds32_pseudo_opcode_hash = hash_new ();
  for ( ; opcode->opcode; opcode++)
    {
      void *op;
      op = hash_find (nds32_pseudo_opcode_hash, opcode->opcode);
      if (op != NULL)
	{
	  as_warn (_("Duplicated pseudo-opcode %s."), opcode->opcode);
	  continue;
	}
      hash_insert (nds32_pseudo_opcode_hash, opcode->opcode, opcode);
    }
}

static struct nds32_pseudo_opcode *
nds32_lookup_pseudo_opcode (char *str)
{
  int i = 0;
  /* Assume pseudo-opcode are less than 16-char in length.  */
  char op[16] = {0};

  for (i = 0; i < (int)ARRAY_SIZE (op); i++)
    {
      if (ISSPACE (op[i] = str[i]))
	break;
    }

  if (i >= (int)ARRAY_SIZE (op))
    return NULL;

  op[i] = '\0';

  return hash_find (nds32_pseudo_opcode_hash, op);
}

static void
nds32_pseudo_opcode_wrapper (char *line, struct nds32_pseudo_opcode *opcode)
{
  int argc = 0;
  char *argv[8] = {NULL};
  char *s;
  char *str = xstrdup (line);

  /* Parse arguments for opcode.  */
  s = str + strlen (opcode->opcode);

  if (!s[0])
    goto end;

  /* Dummy comma to ease separate arguments as below.  */
  s[0] = ',';
  do
    {
      if (s[0] == ',')
	{
	  if (argc >= opcode->argc
	      || (argc >= (int)ARRAY_SIZE (argv) - 1))
	    as_bad (_("Too many argument. `%s'"), line);

	  argv[argc] = s + 1;
	  argc ++;
	  s[0] = '\0';
	}
      ++s;
    } while (s[0] != '\0');
end:
  /* Put the origin line for debugging.  */
  argv[argc] = line;
  opcode->proc (argc, argv, opcode->pseudo_val);
  free (str);
}

/* This function parses CPU specified.  */

static int
nds32_parse_cpu (char *str)
{
  if (nds32_strcasestr (str, "n12") || nds32_strcasestr (str, "n10")
      || nds32_strcasestr (str, "n9") || nds32_strcasestr (str, "n8")
      || nds32_strcasestr (str, "n13"))
    {
      return 1;
    }

  /* Logic here rejects the input CPU model.  */
  as_bad (_("unknown cpu `%s'"), str);
  return 1;
}

/* GAS will call md_parse_option whenever getopt returns an unrecognized code,
   presumably indicating a special code value which appears in md_longopts.
   This function should return non-zero if it handled the option and zero
   otherwise.  There is no need to print a message about an option not being
   recognized.  This will be handled by the generic code.  */

int
nds32_parse_option (int c, char *arg)
{
  switch (c)
    {
    case 'O':
    case OPTION_OPTIMIZE:
      optimize = 1;
      optimize_for_space = 0;
      optimize_for_space_no_align = 0;
      break;
    case OPTION_BIG:
    case OPTION_LITTLE:
      target_big_endian = (c == OPTION_BIG);
      break;
    case OPTION_ABI:
      {
	if (!strcmp (arg, "1"))
	  abi_ver = E_NDS_ABI_V1;
	else if (!strcmp (arg, "2"))
	  abi_ver = E_NDS_ABI_AABI;
	else if (!strcmp (arg, "2fp"))
	  abi_ver = E_NDS_ABI_V2FP;
	else
	  as_bad (_("ABI option must be -mabi={1|2|2fp}"));
	break;
      }
    case OPTION_16BIT:
    case OPTION_NO_16BIT:
      disable_16bit = (c == OPTION_16BIT);
      saved_disable_16bit = (c == OPTION_16BIT);
    case OPTION_EXT_ALL:
      enable_all_ext = 1;
      break;
    case OPTION_EXT_AUDIO:
    case OPTION_NO_EXT_AUDIO:
      enable_audio_extension = (c == OPTION_EXT_AUDIO);
      break;
    case OPTION_EXT_STRING:
    case OPTION_NO_EXT_STRING:
      enable_string_extension = (c == OPTION_EXT_STRING);
      break;
    case OPTION_EXT_MAC:
    case OPTION_NO_EXT_MAC:
      enable_mac_extension = (c == OPTION_EXT_MAC);
      break;
    case OPTION_DIV:
    case OPTION_NO_DIV:
      enable_div_extension = (c == OPTION_DIV);
      break;
    case OPTION_EXT_PERF:
    case OPTION_NO_EXT_PERF:
      enable_c_extension = (c == OPTION_EXT_PERF);
      break;
    case OPTION_EXT_PERF2:
    case OPTION_NO_EXT_PERF2:
      enable_c_extension2 = (c == OPTION_EXT_PERF2);
      break;
    case OPTION_EXT_DSP:
    case OPTION_NO_EXT_DSP:
      enable_dsp_extension = (c == OPTION_EXT_DSP);
      break;
    case OPTION_FPU_SP:
    case OPTION_NO_FPU_SP:
      enable_fpu_sp_extension = (c == OPTION_FPU_SP);
      break;
    case OPTION_FPU_DP:
    case OPTION_NO_FPU_DP:
      enable_fpu_dp_extension = (c == OPTION_FPU_DP);
      break;
    case OPTION_FPU_FMA:
    case OPTION_NO_FPU_FMA:
      enable_fpu_mac_extension = (c == OPTION_FPU_FMA);
      break;
    case OPTION_FPU_FREG:
      switch (atoi (arg))
	{
	case 0: case 4:
	  fs_reg_num = 8;
	  fd_reg_num = 4;
	  fpu_config = E_NDS32_FPU_REG_8SP_4DP << E_NDS32_FPU_REG_CONF_SHIFT;
	  break;
	case 1: case 5:
	  fs_reg_num = 16;
	  fd_reg_num = 8;
	  fpu_config = E_NDS32_FPU_REG_16SP_8DP << E_NDS32_FPU_REG_CONF_SHIFT;
	  break;
	case 2: case 6:
	  fs_reg_num = 32;
	  fd_reg_num = 16;
	  fpu_config = E_NDS32_FPU_REG_32SP_16DP << E_NDS32_FPU_REG_CONF_SHIFT;
	  break;
	case 3: case 7:
	  fs_reg_num = 32;
	  fd_reg_num = 32;
	  fpu_config = E_NDS32_FPU_REG_32SP_32DP << E_NDS32_FPU_REG_CONF_SHIFT;
	  break;
	default:
	  as_bad (_("FPU config option must be -mconfig-fpu={0-7}"));
	  break;
	}
      break;
    case OPTION_REDUCED_REGS:
    case OPTION_NO_REDUCED_REGS:
      enable_reduce_regs = (c == OPTION_REDUCED_REGS);
      break;
    case OPTION_PIC_CODE:
    case OPTION_NO_PIC_CODE:
      pic_code = (c == OPTION_PIC_CODE);
      break;
    case OPTION_OPTIMIZE_SPACE:
      optimize = 0;
      optimize_for_space = 1;
      /* Rufus: Avoid inserting nop16 for label align.  */
      optimize_for_space_no_align = 0;
      break;
    case OPTION_WARN_UNMATCHED:
    case OPTION_NO_WARN_UNMATCHED:
      warn_unmatched_high = (c == OPTION_WARN_UNMATCHED);
      break;
    case OPTION_CPU:
      nds32_parse_cpu (arg);
      break;
    case OPTION_MARCH:
      if (!strcasecmp (arg, "v2"))
	{
	  enable_mac_extension = 1;
	  enable_div_extension = 1;
	  march_cpu_opt = ARCH_V2;
	}
      else if (!strcasecmp (arg, "v3"))
	{
	  enable_mac_extension = 1;
	  enable_div_extension = 1;
	  march_cpu_opt = ARCH_V3;
	}
      else if (!strcasecmp (arg, "v3m"))
	{
	  march_cpu_opt = ARCH_V3M;
	}
      else if (!strcasecmp (arg, "v1"))
	{
	  march_cpu_opt = ARCH_V1;
	}
      else
	{
	  as_bad (_("Baseline option must be -march={v1|v2|v3|v3m}"));
	}
      break;
    case OPTION_DX_REGS:
    case OPTION_NO_DX_REGS:
      enable_dx_regs_extension = (c == OPTION_DX_REGS);
      break;
    case OPTION_NO_RELAX:
      enable_relax_relocs = 0;
      break;
    case OPTION_RELAX_WARN:
      enable_relax_warning = 1;
      break;
    case OPTION_NO_MULCALL_RELAX:
      multi_call_relax = 0;
      break;
    case OPTION_NO_PLTGOT_CALL_RELAX:
      pltgot_call_relax = 0;
      break;
    case OPTION_RELAX_JAL:
      relax_jal_bound = atoi (arg);
      break;
    case OPTION_NO_HINT_FUNC_ARGS:
      use_hint_func_args = 0;
      break;
    case OPTION_NO_OMIT_FP:
      omit_frame_pointer = 0;
      break;
    case OPTION_CONSERVATIVE_IFC:
    case OPTION_NO_CONSERVATIVE_IFC:
      is_conservative_ifc = (c == OPTION_CONSERVATIVE_IFC);
      break;
    case OPTION_ALARM_BLOCK:
      if (!strcmp (arg, "none"))
	alarm_block = ALARM_BLOCK_NONE;
      else if (!strcmp (arg, "bad"))
	alarm_block = ALARM_BLOCK_BAD;
      else if (!strcmp (arg, "fatal"))
	alarm_block = ALARM_BLOCK_FATAL;
      else
	as_bad (_("Alarm block must be -malarm-block={none|bad|fatal}"));
      break;
    case OPTION_B2BB:
    case OPTION_NO_B2BB:
      opt_b2bb = (c == OPTION_B2BB);
      break;
    default:
      return 0;
    }

  return 1;
}

typedef struct insn_label_list
{
  symbolS *label;
  struct insn_label_list *next;
} insn_label_list;

#define INDIRECT_BRANCH_MASK		0x00000001
#define DIRECT_BRANCH_MASK		0x00000002
#define UNCONDITIONAL_BRANCH_MASK	0x00000001
#define CONDITIONAL_BRANCH_MASK		0x00000002

#define IS_FUNC_RETURN_MASK		0x1
#define IS_FUNC_CALL_MASK		0x2
#define IS_COND_FUNC_CALL_MASK		0x3
#define IS_COND_FUNC_RETURN_MASK	0x4

static int ifc_mode = 0;

static int
is_func_branch (int insn_num)
{
  switch (insn_num)
    {
    case NDS32_INSN_IFRET:
      return IS_COND_FUNC_RETURN_MASK;
    case NDS32_INSN_RET:
    case NDS32_INSN_RET5:
    case NDS32_INSN_POP25:
      return IS_FUNC_RETURN_MASK;
    case NDS32_INSN_JAL:
    case NDS32_INSN_JRAL:
    case NDS32_INSN_JRAL5:
      return IS_FUNC_CALL_MASK;
    case NDS32_INSN_IFCALL:
    case NDS32_INSN_IFCALL9:
      return IS_COND_FUNC_CALL_MASK;
    default:
      return 0;
    }
}

static int
is_direct_branch_instruction (int insn_num)
{
  switch (insn_num)
    {
    case NDS32_INSN_J:
    case NDS32_INSN_JAL:
    case NDS32_INSN_IFCALL:
    case NDS32_INSN_IFCALL9:
    case NDS32_INSN_J8:
    case NDS32_INSN_BEQZ:
    case NDS32_INSN_BNEZ:
    case NDS32_INSN_BGEZ:
    case NDS32_INSN_BLTZ:
    case NDS32_INSN_BGTZ:
    case NDS32_INSN_BLEZ:
    case NDS32_INSN_BGEZAL:
    case NDS32_INSN_BLTZAL:
    case NDS32_INSN_BEQ:
    case NDS32_INSN_BNE:
    case NDS32_INSN_BEQZ38:
    case NDS32_INSN_BNEZ38:
    case NDS32_INSN_BEQS38:
    case NDS32_INSN_BNES38:
    case NDS32_INSN_BEQZS8:
    case NDS32_INSN_BNEZS8:
    case NDS32_INSN_BEQC:
    case NDS32_INSN_BNEC:
      return DIRECT_BRANCH_MASK;
    case NDS32_INSN_JR:
    case NDS32_INSN_JR5:
    case NDS32_INSN_IFRET:
    case NDS32_INSN_RET:
    case NDS32_INSN_RET5:
    case NDS32_INSN_POP25:
    case NDS32_INSN_JRAL:
    case NDS32_INSN_JRAL5:
      return INDIRECT_BRANCH_MASK;
    default:
      ;
    }
  return 0;
}

static int
is_conditional_branch_instruction (int insn_num)
{
  switch (insn_num)
    {
    case NDS32_INSN_BEQZ:
    case NDS32_INSN_BNEZ:
    case NDS32_INSN_BGEZ:
    case NDS32_INSN_BLTZ:
    case NDS32_INSN_BGTZ:
    case NDS32_INSN_BLEZ:
    case NDS32_INSN_BGEZAL:
    case NDS32_INSN_BLTZAL:
    case NDS32_INSN_BEQ:
    case NDS32_INSN_BNE:
    case NDS32_INSN_BEQZ38:
    case NDS32_INSN_BNEZ38:
    case NDS32_INSN_BEQS38:
    case NDS32_INSN_BNES38:
    case NDS32_INSN_BEQZS8:
    case NDS32_INSN_BNEZS8:
    case NDS32_INSN_IFRET:
    case NDS32_INSN_BEQC:
    case NDS32_INSN_BNEC:
      return CONDITIONAL_BRANCH_MASK;
    case NDS32_INSN_J:
    case NDS32_INSN_JAL:
    case NDS32_INSN_IFCALL:
    case NDS32_INSN_IFCALL9:
    case NDS32_INSN_J8:
    case NDS32_INSN_JR:
    case NDS32_INSN_JR5:
    case NDS32_INSN_RET:
    case NDS32_INSN_RET5:
    case NDS32_INSN_POP25:
    case NDS32_INSN_JRAL:
    case NDS32_INSN_JRAL5:
      return UNCONDITIONAL_BRANCH_MASK;
    default:
      ;
    }
  return 0;
}

static int
is_lo12_mem_reg_instruction (int insn_num)
{
  switch (insn_num)
    {
    case NDS32_INSN_LB:
    case NDS32_INSN_LBS:
    case NDS32_INSN_LH:
    case NDS32_INSN_LHS:
    case NDS32_INSN_LW:
    case NDS32_INSN_SB:
    case NDS32_INSN_SH:
    case NDS32_INSN_SW:
      return 1;
    default:
      ;
    }
  return 0;
}

static int
is_lo12_mem_imm_instruction (int insn_num)
{
  switch (insn_num)
    {
    case NDS32_INSN_LBI:
    case NDS32_INSN_LHI:
    case NDS32_INSN_LWI:
    case NDS32_INSN_LBSI:
    case NDS32_INSN_LHSI:
    case NDS32_INSN_SBI:
    case NDS32_INSN_SHI:
    case NDS32_INSN_SWI:
    case NDS32_INSN_FLSI:
    case NDS32_INSN_FLDI:
    case NDS32_INSN_FSSI:
    case NDS32_INSN_FSDI:
      return 1;
    default:
      ;
    }
  return 0;
}

static int
is_hint_func_args (int hint_p, int regP)
{
  return hint_p & (1 << regP);
}

/* Branch instruction attribute (end).  */
typedef struct dep_node dep_node;
typedef struct nds32_insn_instant nds32_insn_instant;
typedef struct nds32_insn_list nds32_insn_list;
typedef struct basic_block basic_block;
typedef struct nds32_bb_list nds32_bb_list;
typedef struct reloc_tree_node reloc_tree_node;
typedef struct bfdsym_bb_map bfdsym_bb_map;
typedef struct lp_bb_node lp_bb_node;

static nds32_insn_instant *prev_insn_s;
static reloc_tree_node *nds32_reloc_node_pool;
static lp_bb_node *lp_bb_node_list = NULL;

static void init_insn_list (void);
static nds32_insn_list *get_free_insn_list (void);
static void push_insn_to_list (nds32_insn_list **, nds32_insn_instant *);
static void push_to_insn_list_all (nds32_insn_list **, nds32_insn_list **);
static void free_nds32_insn_list (nds32_insn_list **);

static void append_basic_block (basic_block **);
static void create_new_basic_block (void);
static void init_basic_block (void);
static nds32_bb_list *get_free_bb_list (void);
static void push_to_bb_list_all (nds32_bb_list **, nds32_bb_list **);
static void push_bb_to_bb_list (nds32_bb_list **, basic_block *);

static void free_nds32_reloc_node_list (reloc_tree_node *, reloc_tree_node *);
static reloc_tree_node *fetch_reloc_node_from_pool (void);
static void return_reloc_node_to_pool (reloc_tree_node *);
static void free_reloc_node_sibling (reloc_tree_node **);
static void free_reloc_node_next (reloc_tree_node *);
static reloc_tree_node *new_reloc_node_sibling (reloc_tree_node *,
						nds32_insn_instant *);
static void bind_reloc_list_insn (reloc_tree_node *);
static void bind_reloc_node_child_sibling (reloc_tree_node *,
					   reloc_tree_node *);
static void taint_reloc_node_tree (reloc_tree_node *);
static void insert_relax_type (nds32_insn_instant *insn_p, int reloc_type,
			       int data_size, int arg, expressionS *exp_p);

static void
init_cfg_var (void)
{
  init_basic_block ();
  prev_insn_s = NULL;
  init_insn_list ();
  nds32_reloc_node_pool = NULL;
}

/* dep_node
   Record the use of the general purpose register.  */

struct dep_node
{
  short reg_num;
  short flag;
  struct dep_node *next;
#define CGEN_OPINST_INPUT_MASK 0x00000001
#define CGEN_OPINST_OUTPUT_MASK 0x00000002
};


/* Record the use of the instructions.  */

struct nds32_insn_instant
{
  /* Opcode of this instruction.  */
  enum cgen_insn_type insn_num;
  char *addr;
  fragS *frag;
  int num_fixups;
  fixS *fixups[GAS_CGEN_MAX_FIXUPS];
  /* Operands of this instructions.  */
  dep_node *gr_dep_list;
  /* Where his instruction belongs to.  */
  basic_block *parent;
  struct nds32_insn_instant *next;
  struct nds32_insn_instant *prev;
  short byte_sz;
  short insn_sz;
  int hint_func_args;
  int md_relax;
  reloc_tree_node *reloc_node;
};

/* A list used to chain several instructions
   with the same attribute up.  */

struct nds32_insn_list
{
  nds32_insn_instant *insn;
  struct nds32_insn_list *next;
};

static nds32_insn_list *nds32_hi_insn_list;
static nds32_insn_list *nds32_got20_insn_list;
static nds32_insn_list *nds32_slt_insn_list;
static nds32_insn_list *nds32_free_insn_list;
static nds32_insn_list *nds32_ta_insn_list;

static void
init_insn_list (void)
{
  nds32_hi_insn_list = NULL;
  nds32_got20_insn_list = NULL;
  nds32_slt_insn_list = NULL;
  nds32_ta_insn_list = NULL;
  nds32_free_insn_list = NULL;
}

static nds32_insn_list *
get_free_insn_list (void)
{
  nds32_insn_list *tmp_insn_list;

  if (nds32_free_insn_list == NULL)
    return xmalloc (sizeof (nds32_insn_list));

  tmp_insn_list = nds32_free_insn_list;
  nds32_free_insn_list = nds32_free_insn_list->next;
  return tmp_insn_list;
}

static void
push_insn_to_list (nds32_insn_list ** insn_list_p,
		   nds32_insn_instant *insn_p)
{
  nds32_insn_list *tmp_list = get_free_insn_list ();
  tmp_list->insn = insn_p;
  tmp_list->next = *insn_list_p;
  *insn_list_p = tmp_list;
}

static void
push_to_insn_list_all (nds32_insn_list ** insn_list_p,
		       nds32_insn_list ** insn_list_q)
{
  nds32_insn_list *insn_list_t = *insn_list_p;

  if (insn_list_t == NULL)
    return;

  while (insn_list_t->next != NULL)
    insn_list_t = insn_list_t->next;

  insn_list_t->next = *insn_list_q;
  *insn_list_q = *insn_list_p;
  *insn_list_p = NULL;
}

static void
free_nds32_insn_list (nds32_insn_list ** insn_list_p)
{
  nds32_insn_list *insn_list_s, *insn_list_s2;

  insn_list_s = *insn_list_p;
  while (insn_list_s != NULL)
    {
      insn_list_s2 = insn_list_s->next;
      xfree (insn_list_s);
      insn_list_s = insn_list_s2;
    }
  *insn_list_p = NULL;
}


/* Record the use of a basic block.  */

struct basic_block
{
  /* Chaining all the basic blocks.  */
  struct basic_block *list_next;
  struct basic_block *list_prev;

  /* The first instruction in this basic block.  */
  nds32_insn_instant *insn_head;
  /* The last instruction in this basic block.  */
  nds32_insn_instant *insn_tail;

  /* Next direct bb.  For these are sperated by labels
     or target of non-taken branches.  */
  struct basic_block *cfg_next;
  /* Target of taken branches.  */
  struct basic_block *cfg_target;
  /* cfg_next and cfg_target are illustrated as below.
                                   cfg_next   cfg_target   list_next
         [ bb1 ] ...                bb2         -
     .L0:[ bb2 ] ...                bb3         -
         [ bb3 ] beqz  $r0, .L1     bb4        bb5
         [ bb4 ] jal   foo           -         foo          bb5
     .L1:[ bb5 ] j     .L0           -         bb2

   */

  struct lp_bb_node *lp_node;
  insn_label_list *label_list;
  frchainS *frchain_now;
  segT now_seg;
  nds32_insn_instant *set_before_use_gr[32];
  nds32_insn_instant *use_before_set_gr[32];
  int known_pred;
  int walk_through;
  int in_critical;
  int in_common;
  char *filename;
  unsigned int line_num;
  unsigned int index;
};

/*
 bb_list     - global basic block list
 bb_now      - current basic block
 bb_indirect - just a dummy mark for unknow basic block (indirect jump)

     <- - - list_prev
 bb_list-> b0 -> b1 -> b2 -> bb_now
            list_next - - ->
 */
static basic_block *bb_indirect;
static basic_block *bb_list;
static basic_block *bb_now;

/* A list used to chain several basic blocks with the same attribute up.  */
struct nds32_bb_list
{
  basic_block *bb;
  struct
  {
    int walk_through;
    int in_critical;
  } trace_data;
  nds32_bb_list *next;
};

static nds32_bb_list *nds32_free_bb_list;
/* nds32_use_bb_list includes all the path we've traversed.  */
static nds32_bb_list *nds32_use_bb_list;
/* nds32_path_bb_list is the path to reach current basic-block.  */
static nds32_bb_list *nds32_path_bb_list;

static void
append_basic_block (basic_block ** bb_p)
{
  basic_block *bb_new = xmalloc (sizeof (basic_block));
  bb_new->list_prev = *bb_p;
  bb_new->cfg_target = NULL;
  bb_new->insn_head = NULL;
  bb_new->insn_tail = NULL;
  bb_new->label_list = NULL;
  bb_new->lp_node = NULL;

  memset (&bb_new->set_before_use_gr, 0, 32 * sizeof (nds32_insn_instant *));
  memset (&bb_new->use_before_set_gr, 0, 32 * sizeof (nds32_insn_instant *));

  if ((*bb_p) != NULL)
    {
      if ((*bb_p)->list_next != NULL)
	{
	  (*bb_p)->list_next->list_prev = bb_new;
	}
      bb_new->list_next = (*bb_p)->list_next;
      bb_new->cfg_next = (*bb_p)->cfg_next;
      (*bb_p)->list_next = bb_new;
      (*bb_p)->cfg_next = bb_new;
    }
  else
    {
      bb_new->list_next = NULL;
      bb_new->cfg_next = NULL;
      *bb_p = bb_new;
    }
  bb_new->frchain_now = frchain_now;
  bb_new->known_pred = 0;
  bb_new->walk_through = 0;
  bb_new->in_critical = 0;
  bb_new->in_common = 0;
  bb_new->now_seg = now_seg;
  as_where (&bb_new->filename, &bb_new->line_num);
}

static void
create_new_basic_block (void)
{
  append_basic_block (&bb_now);
  bb_now = bb_now->list_next;
}

static void
init_basic_block (void)
{
  bb_now = NULL;
  append_basic_block (&bb_now);
  bb_list = bb_now;
  bb_indirect = NULL;
  append_basic_block (&bb_indirect);
}

static nds32_bb_list *
get_free_bb_list (void)
{
  nds32_bb_list *tmp_bb_list;

  if (nds32_free_bb_list == NULL)
    return xmalloc (sizeof (nds32_bb_list));

  tmp_bb_list = nds32_free_bb_list;
  nds32_free_bb_list = nds32_free_bb_list->next;
  return tmp_bb_list;
}

static void
push_to_bb_list_all (nds32_bb_list ** bb_list_p, nds32_bb_list ** bb_list_q)
{
  nds32_bb_list *bb_list_t = *bb_list_p;

  if (bb_list_t == NULL)
    return;

  while (bb_list_t->next != NULL)
    bb_list_t = bb_list_t->next;

  bb_list_t->next = *bb_list_q;
  *bb_list_q = bb_list_t;
  *bb_list_p = NULL;
}

static void
push_bb_to_bb_list (nds32_bb_list ** bb_list_p, basic_block *bb_p)
{
  nds32_bb_list *bb_list_t = get_free_bb_list ();
  bb_list_t->bb = bb_p;
  bb_list_t->next = *bb_list_p;
  *bb_list_p = bb_list_t;
}

static void
pop_bb_from_bb_list (nds32_bb_list ** bb_list_p)
{
  nds32_bb_list *bb_list_t;

  if (!(*bb_list_p))
    return;

  bb_list_t = *bb_list_p;
  *bb_list_p = (*bb_list_p)->next;
  bb_list_t->next = nds32_free_bb_list;
  nds32_free_bb_list = bb_list_t;
}

static void
bb_list_in_critical (nds32_bb_list *bb_list_p)
{
  nds32_bb_list *bb_list_t;

  bb_list_t = bb_list_p;
  while (bb_list_t)
    {
      bb_list_t->bb->in_critical = 1;
      bb_list_t = bb_list_t->next;
    }
}

static int
check_unknown_source_in_critical (nds32_bb_list *bb_list_p)
{
  nds32_bb_list *bb_list_t;

  bb_list_t = bb_list_p;
  while (bb_list_t)
    {
      if (bb_list_t->bb->in_critical)
	{
	  if ((bb_list_t->bb->known_pred - bb_list_t->bb->in_common) >
	      bb_list_t->bb->walk_through)
	    return FALSE;
	}
      bb_list_t = bb_list_t->next;
    }
  return TRUE;
}

static void
clean_temp_var_bb_list (nds32_bb_list *bb_list_p)
{
  nds32_bb_list *bb_list_t;

  bb_list_t = bb_list_p;
  while (bb_list_t)
    {
      bb_list_t->bb->walk_through = 0;
      bb_list_t->bb->in_critical = 0;
      bb_list_t = bb_list_t->next;
    }
}

static void
save_temp_var_bb_list (nds32_bb_list *bb_list_p)
{
  nds32_bb_list *bb_list_t;

  bb_list_t = bb_list_p;
  while (bb_list_t)
    {
      bb_list_t->trace_data.walk_through = bb_list_t->bb->walk_through;
      bb_list_t->trace_data.in_critical = bb_list_t->bb->in_critical;
      bb_list_t = bb_list_t->next;
    }
}

static void
restore_temp_var_bb_list (nds32_bb_list *bb_list_p)
{
  nds32_bb_list *bb_list_t;

  bb_list_t = bb_list_p;
  while (bb_list_t)
    {
      bb_list_t->bb->walk_through = bb_list_t->trace_data.walk_through;
      bb_list_t->bb->in_critical = bb_list_t->trace_data.in_critical;
      bb_list_t = bb_list_t->next;
    }
}


/* A structure used to record some fixups may be appended
   to the instruction.  */
struct reloc_tree_node
{
  int reloc_type;
  int type_mask;
  int leaf_num;
  nds32_insn_instant *insn;
  reloc_tree_node *parent;
  reloc_tree_node *child;
  reloc_tree_node *sibling;
  reloc_tree_node *next;
  short tainted;
  short convertible;
};

#define MAX_PATTERN_LEN 4
static reloc_tree_node *reloc_list_now;
static reloc_tree_node *current_pattern[MAX_PATTERN_LEN];

static void
free_nds32_reloc_node_list (reloc_tree_node *reloc_list_p,
			    reloc_tree_node *delimiter)
{
  reloc_tree_node *reloc_list_t;

  while (reloc_list_p != delimiter)
    {
      reloc_list_t = reloc_list_p;
      reloc_list_p = reloc_list_p->next;
      free (reloc_list_t);
    }
}

static reloc_tree_node *
fetch_reloc_node_from_pool (void)
{
  reloc_tree_node *reloc_node_t;

  if (!nds32_reloc_node_pool)
    return (reloc_tree_node *) calloc (1, sizeof (reloc_tree_node));

  reloc_node_t = nds32_reloc_node_pool;
  nds32_reloc_node_pool = nds32_reloc_node_pool->next;
  return reloc_node_t;
}

static void
return_reloc_node_to_pool (reloc_tree_node *reloc_node_p)
{
  reloc_tree_node *reloc_node_t;
  if (!reloc_node_p)
    return;

  reloc_node_t = reloc_node_p->next;
  reloc_node_p->next = nds32_reloc_node_pool;
  nds32_reloc_node_pool = reloc_node_t;
}

static void
free_reloc_node_sibling (reloc_tree_node ** reloc_node_p)
{
  reloc_tree_node *reloc_node_t = *reloc_node_p;

  while (reloc_node_t)
    {
      return_reloc_node_to_pool (reloc_node_t);
      reloc_node_t = reloc_node_t->sibling;
    }
  *reloc_node_p = NULL;
}

static void
free_reloc_node_next (reloc_tree_node *reloc_node_p)
{
  reloc_tree_node *reloc_node_t = reloc_node_p;

  while (reloc_node_t)
    {
      return_reloc_node_to_pool (reloc_node_t);
      reloc_node_t = reloc_node_t->next;
    }
}

static reloc_tree_node *
new_reloc_node_sibling (reloc_tree_node *list_head,
			nds32_insn_instant *insn_p)
{
  reloc_tree_node *reloc_node_t = fetch_reloc_node_from_pool ();

  memset (reloc_node_t, 0, sizeof (reloc_tree_node));
  reloc_node_t->sibling = list_head;
  reloc_node_t->insn = insn_p;
  return reloc_node_t;
}

static void
bind_reloc_list_insn (reloc_tree_node *reloc_node_p)
{
  reloc_tree_node *reloc_node_t = reloc_node_p;

  reloc_node_t->next = reloc_node_t->insn->reloc_node;
  reloc_node_t->insn->reloc_node = reloc_node_t;
}

static void
bind_reloc_node_child_sibling (reloc_tree_node *reloc_parent,
			       reloc_tree_node *reloc_child)
{
  reloc_parent->child = reloc_child;

  while (reloc_child != NULL)
    {
      reloc_child->parent = reloc_parent;
      reloc_child = reloc_child->sibling;
    }
}

static void
taint_reloc_node_tree (reloc_tree_node *reloc_node_p)
{
  reloc_tree_node *reloc_node_t;

  if (reloc_node_p->tainted)
    return;

  reloc_node_t = reloc_node_p->parent;

  /* If reloc_node_p is root, taint the root node.
     Otherwise, taint all siblings of reloc_node_p.  */
  if (reloc_node_t)
    reloc_node_t = reloc_node_t->child;
  else
    reloc_node_t = reloc_node_p;

  while (reloc_node_t)
    {
      reloc_node_t->tainted = 1;
      reloc_node_t = reloc_node_t->sibling;
    }
}

struct bfdsym_bb_map
{
  asymbol *bfdsym;
  basic_block *bb;
  bfdsym_bb_map *next;
};

static bfdsym_bb_map *
new_bfdsym_bb_map (basic_block *bb_p, asymbol *bfdsym_p,
		   bfdsym_bb_map *next_p)
{
  bfdsym_bb_map *bfdsym_bb_map_t;

  bfdsym_bb_map_t = xmalloc (sizeof (bfdsym_bb_map));
  bfdsym_bb_map_t->bb = bb_p;
  bfdsym_bb_map_t->bfdsym = bfdsym_p;
  bfdsym_bb_map_t->next = next_p;

  return bfdsym_bb_map_t;

}

static bfdsym_bb_map *
find_bfdsym_bb_map (bfdsym_bb_map *map_list_p, asymbol *bfdsym_p)
{
  while (map_list_p != NULL)
    {
      if (map_list_p->bfdsym == bfdsym_p)
	return map_list_p;
      map_list_p = map_list_p->next;
    }

  return NULL;
}

static void
bfdsym_bb_map_delete (const char *key ATTRIBUTE_UNUSED, PTR bfdsym_bb_map_p)
{
  bfdsym_bb_map *bfdsym_bb_map_t = bfdsym_bb_map_p, *bfdsym_bb_map_t2 =
    bfdsym_bb_map_p;

  while (bfdsym_bb_map_t2 != NULL)
    {
      bfdsym_bb_map_t = bfdsym_bb_map_t2->next;
      xfree (bfdsym_bb_map_t2);
      bfdsym_bb_map_t2 = bfdsym_bb_map_t;
    }
}


/* Record basic blocks of landing pads recorded in .gcc_except_table.  */
struct lp_bb_node
{
  basic_block *bb;
  lp_bb_node *next;
};

static void
clean_lp_bb_list (lp_bb_node *lp_bb_list)
{
  lp_bb_node *node_t, *node_t2;

  node_t = lp_bb_list;
  while (node_t)
    {
      node_t2 = node_t;
      node_t = node_t->next;
      free (node_t2);
    }
}

/* tc_check_label  */

void
nds32_check_label (symbolS *label ATTRIBUTE_UNUSED)
{
  /* The code used to create BB is move to frob_label.
     They should go there.  */
}

static void
little (int on)
{
  target_big_endian = !on;
}

/* These functions toggles the generation of 16-bit.  First encounter signals
   the beginning of not generating 16-bit instructions and next encounter
   signals the restoring back to default behavior.  */

static void
restore_16bit (int ignore ATTRIBUTE_UNUSED)
{
  disable_16bit = saved_disable_16bit;
}

static void
off_16bit (int ignore ATTRIBUTE_UNUSED)
{
  /* Save default 16-bit conversion setting and turn the conversion off.  */
  saved_disable_16bit = disable_16bit;
  disable_16bit = 1;
}

enum
{
  NDS32_SEC_NONE,
  NDS32_SEC_SDATA_SBSS,
  NDS32_SEC_EFLAG_ISR,
  NDS32_SEC_MAX
};

static segT sec_eflag = NULL;

static void
create_nds32_seg (int nds32_sec_type)
{

  switch (nds32_sec_type)
    {
    case NDS32_SEC_SDATA_SBSS:
      break;
    case NDS32_SEC_EFLAG_ISR:
      {
	segT sec_t;

	sec_eflag = sec_t = subseg_new (".nds32_e_flags", (subsegT) 0);

	bfd_set_section_flags (stdoutput, sec_t,
			       SEC_HAS_CONTENTS | SEC_READONLY);

	bfd_set_section_alignment (stdoutput, sec_t, 2);
      }
      break;
    default:
      break;
    }
}

/* Built-in segments for small object.  */
typedef struct nds32_seg_entryT
{
  segT s;
  const char *name;
  flagword flags;
} nds32_seg_entry;

nds32_seg_entry nds32_seg_table[] = {
  {NULL, ".sdata_f",
   SEC_ALLOC | SEC_LOAD | SEC_RELOC | SEC_DATA | SEC_HAS_CONTENTS |
   SEC_SMALL_DATA},
  {NULL, ".sdata_b",
   SEC_ALLOC | SEC_LOAD | SEC_RELOC | SEC_DATA | SEC_HAS_CONTENTS |
   SEC_SMALL_DATA},
  {NULL, ".sdata_h",
   SEC_ALLOC | SEC_LOAD | SEC_RELOC | SEC_DATA | SEC_HAS_CONTENTS |
   SEC_SMALL_DATA},
  {NULL, ".sdata_w",
   SEC_ALLOC | SEC_LOAD | SEC_RELOC | SEC_DATA | SEC_HAS_CONTENTS |
   SEC_SMALL_DATA},
  {NULL, ".sdata_d",
   SEC_ALLOC | SEC_LOAD | SEC_RELOC | SEC_DATA | SEC_HAS_CONTENTS |
   SEC_SMALL_DATA},
  {NULL, ".sbss_f", SEC_ALLOC | SEC_SMALL_DATA},
  {NULL, ".sbss_b", SEC_ALLOC | SEC_SMALL_DATA},
  {NULL, ".sbss_h", SEC_ALLOC | SEC_SMALL_DATA},
  {NULL, ".sbss_w", SEC_ALLOC | SEC_SMALL_DATA},
  {NULL, ".sbss_d", SEC_ALLOC | SEC_SMALL_DATA}
};

/* Indexes to nds32_seg_table[].  */
enum NDS32_SECTIONS_ENUM
{
  SDATA_F_SECTION = 0,
  SDATA_B_SECTION = 1,
  SDATA_H_SECTION = 2,
  SDATA_W_SECTION = 3,
  SDATA_D_SECTION = 4,
  SBSS_F_SECTION = 5,
  SBSS_B_SECTION = 6,
  SBSS_H_SECTION = 7,
  SBSS_W_SECTION = 8,
  SBSS_D_SECTION = 9
};

/* COLE: The following code is borrowed from v850_seg.
	 Revise this is needed.  */

static void
do_nds32_seg (int i, subsegT sub)
{
  nds32_seg_entry *seg = nds32_seg_table + i;

  obj_elf_section_change_hook ();

  if (seg->s != NULL)
    subseg_set (seg->s, sub);
  else
    {
      seg->s = subseg_new (seg->name, sub);
      if (OUTPUT_FLAVOR == bfd_target_elf_flavour)
	{
	  bfd_set_section_flags (stdoutput, seg->s, seg->flags);
	  if ((seg->flags & SEC_LOAD) == 0)
	    seg_info (seg->s)->bss = 1;
	}
    }
}

static void
nds32_seg (int i)
{
  subsegT sub = get_absolute_expression ();

  do_nds32_seg (i, sub);
  demand_empty_rest_of_line ();
}

/* Set if label adjustment is needed.  I should not adjust .xbyte in dwarf.  */
static symbolS *nds32_last_label;	/* Last label for aligment.  */

/* This code is referred from D30V for adjust label to be with pedning
   aligment.  For example,
     LBYTE: .byte	0x12
     LHALF: .half	0x12
     LWORD: .word	0x12
   Without this, the above label will not attatch to incoming data.  */

static void
nds32_adjust_label (int n)
{
  /* FIXME: I think adjust lable and alignment is
     the programmer's obligation.  Saddly, VLSI team doesn't
     properly use .align for their test cases.
     So I re-implement cons_align and auto adjust labels, again.

     I think d30v's implmentation is simple and good enough.  */

  symbolS *label = nds32_last_label;
  nds32_last_label = NULL;

  /* SEC_ALLOC is used to eliminate .debug_ sections.
     SEC_CODE is used to include section for ILM.  */
  if (((now_seg->flags & SEC_ALLOC) == 0 && (now_seg->flags & SEC_CODE) == 0)
      || strcmp (now_seg->name, ".eh_frame") == 0
      || strcmp (now_seg->name, ".gcc_except_table") == 0)
    return;

  /* Only frag by alignment when needed.
     Otherwise, it will fail to optimize labels on 4-byte boundary.  (bug8454)
     See md_convert_frag () and RELAX_SET_RELAXABLE (frag) for details.  */
  if (frag_now_fix () & ((1 << n) -1 ))
    {
      if (subseg_text_p (now_seg))
	frag_align_code (n, 0);
      else
	frag_align (n, 0, 0);

      /* Record the minimum alignment for this segment.  */
      record_alignment (now_seg, n - OCTETS_PER_BYTE_POWER);
    }

  if (label != NULL)
    {
      symbolS *sym;
      int label_seen = FALSE;
      struct frag *old_frag;
      valueT old_value, new_value;

      gas_assert (S_GET_SEGMENT (label) == now_seg);

      old_frag  = symbol_get_frag (label);
      old_value = S_GET_VALUE (label);
      new_value = (valueT) frag_now_fix ();

      /* Multiple labels may be on the same address.  And the last symbol
	 may not be a label at all, e.g., register name, external function names,
	 so I have to track the last label in tc_frob_label instead of
	 just using symbol_lastP.  */
      for (sym = symbol_lastP; sym != NULL; sym = symbol_previous (sym))
	{
	  if (symbol_get_frag (sym) == old_frag
	      && S_GET_VALUE (sym) == old_value)
	    {
	      /* Warning HERE! */
	      label_seen = TRUE;
	      symbol_set_frag (sym, frag_now);
	      S_SET_VALUE (sym, new_value);
	    }
	  else if (label_seen && symbol_get_frag (sym) != old_frag)
	    break;
	}
    }
}

void
nds32_cons_align (int size ATTRIBUTE_UNUSED)
{
  /* COLE, Mar 24, 2012

     Do nothing here.
     This is called before `md_flush_pending_output' is called by `cons'.

     There are two things should be done for auto-adjust-label.
     1. Align data/instructions and adjust label to be attached to them.
     2. Clear auto-adjust state, so incommng data/instructions will not
	adjust the label.

     For example,
	  .byte 0x1
	.L0:
	  .word 0x2
	  .word 0x3
     in this case, '.word 0x2' will adjust the label, .L0, but '.word 0x3' should not.

     I think `md_flush_pending_output' is a good place to clear the auto-adjust state,
     but it is also called by `cons' before this function.
     To simplify the code, instead of overriding .zero, .fill, .space, etc,
     I think we should just adjust label in `nds32_aligned_X_cons' instead of here.  */
}

static void
nds32_aligned_cons (int idx)
{
  nds32_adjust_label (idx);
  /* Call default handler.  */
  cons (1 << idx);
  if (now_seg->flags & SEC_CODE
      && now_seg->flags & SEC_ALLOC && now_seg->flags & SEC_RELOC)
    {
      /* Use BFD_RELOC_NDS32_DATA to avoid EX9 optimization replacing data.  */
      expressionS exp;
      fixS *fixP;

      exp.X_add_number = 0;
      exp.X_op = O_constant;
      fixP = fix_new_exp (frag_now, frag_now_fix (), 0, &exp, 0,
			  BFD_RELOC_NDS32_DATA);
      fixP->fx_where -= (1 << idx);
      fixP->fx_size = (1 << idx);
    }
}

/* `.double' directive. */

static void
nds32_aligned_float_cons (int type)
{
  switch (type)
    {
    case 'f':
    case 'F':
    case 's':
    case 'S':
      nds32_adjust_label (2);
      break;
    case 'd':
    case 'D':
    case 'r':
    case 'R':
      nds32_adjust_label (4);
      break;
    default:
      as_bad ("Unrecognized float type, %c\n", (char)type);
    }
  /* Call default handler.  */
  float_cons (type);
}

static void
nds32_pic (int ignore ATTRIBUTE_UNUSED)
{
  /* Another way to do -mpic.
     This is for GCC internal use and should always be first line
     of code, otherwise, the effect is not determined.  */
  pic_code = 1;
}

static void
nds32_abi (int ver)
{
  /* Another way to do -mabi.
     This is for GCC internal use and should always be at the beginning
     of code, otherwise, the effect is not determined.  */
  abi_ver = ver;
}

static void
nds32_relax_relocs (int relax)
{
  char saved_char;
  char *name;
  int i;
  char *subtype_relax[] =
  {"", "", "ex9", "ifc"};

  name = input_line_pointer;
  while (*input_line_pointer && !ISSPACE (*input_line_pointer))
    input_line_pointer++;
  saved_char = *input_line_pointer;
  *input_line_pointer = 0;

  for (i = 0; i < (int) ARRAY_SIZE(subtype_relax); i++)
    {
	if (strcmp (name, subtype_relax[i]) == 0)
	{
	  switch (i)
	    {
	    case 0:
	    case 1:
	      enable_relax_relocs = relax & enable_relax_relocs;
	      enable_relax_ex9 = relax & enable_relax_ex9;
	      enable_relax_ifc = relax & enable_relax_ifc;
	      break;
	    case 2:
	      enable_relax_ex9 = relax;
	      break;
	    case 3:
	      enable_relax_ifc = relax;
	      break;
	    default:
	      break;
	    }
	    break;
	}
    }
  *input_line_pointer = saved_char;
  ignore_rest_of_line ();
}

/* Record which arguments register($r0 ~ $r5) is not used in callee.
   bit[i] for $ri  */

static void
nds32_set_hint_func_args (int ignore ATTRIBUTE_UNUSED)
{
  expressionS exp;

  expression (&exp);
  if (!use_hint_func_args)
    return;

  if (exp.X_op == O_constant)
    {
      if (exp.X_add_number >= 0 && exp.X_add_number < (1 << 6))
	hint_func_args = exp.X_add_number;
      else
	as_warn (_("[gas error] Argument of .hint_func_args is out of range : %x."),
		 (unsigned int) exp.X_add_number);
    }
  else
    as_warn (_("[gas error] Argument of .hint_func_args is not a constant."));
}

/* Insert relocations to mark the begin and end of a fp-omitted function,
   for further relaxation use.
   bit[i] for $ri  */

static void
nds32_omit_fp_begin (int mode)
{
  expressionS exp;

  if (omit_frame_pointer == 0)
    return;
  exp.X_op = O_symbol;
  exp.X_add_symbol = abs_section_sym;
  if (mode == 1)
    {
      exp.X_add_number = R_NDS32_RELAX_REGION_OMIT_FP_FLAG;
      fix_new_exp (frag_now, frag_now_fix (), 0, &exp, 0,
		   BFD_RELOC_NDS32_RELAX_REGION_BEGIN);
    }
  else
    {
      exp.X_add_number = R_NDS32_RELAX_REGION_OMIT_FP_FLAG;
      fix_new_exp (frag_now, frag_now_fix (), 0, &exp, 0,
		   BFD_RELOC_NDS32_RELAX_REGION_END);
    }
}

/* Insert relocations to mark the begin and end of ex9 region,
   for further relaxation use.
   bit[i] for $ri */

static void
nds32_no_ex9_begin (int mode)
{
  expressionS exp;

  exp.X_op = O_symbol;
  exp.X_add_symbol = abs_section_sym;
  if (mode == 1)
    {
      exp.X_add_number = R_NDS32_RELAX_REGION_NO_EX9_FLAG;
      fix_new_exp (frag_now, frag_now_fix (), 0, &exp, 0,
		   BFD_RELOC_NDS32_RELAX_REGION_BEGIN);
    }
  else
    {
      exp.X_add_number = R_NDS32_RELAX_REGION_NO_EX9_FLAG;
      fix_new_exp (frag_now, frag_now_fix (), 0, &exp, 0,
		   BFD_RELOC_NDS32_RELAX_REGION_END);
    }
}

static void
nds32_loop_begin (int mode)
{
  /* Insert loop region relocation here.  */
  expressionS exp;

  exp.X_op = O_symbol;
  exp.X_add_symbol = abs_section_sym;
  if (mode == 1)
    {
      exp.X_add_number = R_NDS32_RELAX_REGION_INNERMOST_LOOP_FLAG;
      fix_new_exp (frag_now, frag_now_fix (), 0, &exp, 0,
		   BFD_RELOC_NDS32_RELAX_REGION_BEGIN);
    }
  else
    {
      exp.X_add_number = R_NDS32_RELAX_REGION_INNERMOST_LOOP_FLAG;
      fix_new_exp (frag_now, frag_now_fix (), 0, &exp, 0,
		   BFD_RELOC_NDS32_RELAX_REGION_END);
    }
}

/* Decide the size of vector entries, only accepts 4 or 16 now.  */

static void
nds32_vec_size (int ignore ATTRIBUTE_UNUSED)
{
  expressionS exp;

  expression (&exp);

  if (exp.X_op == O_constant)
    {
      if (exp.X_add_number == 4 || exp.X_add_number == 16)
	{
	  if (vec_size == 0)
	    vec_size = exp.X_add_number;
	  else if (vec_size != exp.X_add_number)
	    as_warn (_("[gas warn] Different arguments of .vec_size are found, "
		       "previous %d, current %d"),
		     (int) vec_size,
		     (int) exp.X_add_number);
	}
      else
	as_warn (_("[gas warn] Argument of .vec_size is expected 4 or 16, actual: %d."),
		 (int) exp.X_add_number);
    }
  else
    as_warn (_("[gas warn] Argument of .vec_size is not a constant."));
}

/* The behavior of ".flag" directive varies depending on the target.
   In nds32 target, we use it to recognize whether this assembly content is
   generated by compiler.  Other features can also be added in this function
   in the future. */

static void
nds32_flag (int ignore ATTRIBUTE_UNUSED)
{
  char *name;
  char saved_char;
  int i;
  char *possible_flags[] = {"compiler_generated_asm"};

  /* Skip whitespaces.  */
  name = input_line_pointer;
  while (*input_line_pointer && !ISSPACE (*input_line_pointer))
    input_line_pointer++;
  saved_char = *input_line_pointer;
  *input_line_pointer = 0;

  for (i = 0; i < (int) ARRAY_SIZE (possible_flags); i++)
    {
      if (strcmp (name, possible_flags[i]) == 0)
	{
	  switch (i)
	    {
	    case 0:
	      /* flag: compiler_generated_asm */
	      compiler_generated_asm = 1;
	      break;
	    default:
	      break;
	    }
	  break; /* Already found the flag, no need to continue next loop.   */
	}
    }

  *input_line_pointer = saved_char;
  ignore_rest_of_line ();
}

/* The target specific pseudo-ops which we support.  */
const pseudo_typeS md_pseudo_table[] = {
  /* Forced alignment if declared these ways.  */
  {"ascii", stringer, 8 + 0},
  {"asciz", stringer, 8 + 1},
  {"double", nds32_aligned_float_cons, 'd'},
  {"dword", nds32_aligned_cons, 3},
  {"float", nds32_aligned_float_cons, 'f'},
  {"half", nds32_aligned_cons, 1},
  {"hword", nds32_aligned_cons, 1},
  {"int", nds32_aligned_cons, 2},
  {"long", nds32_aligned_cons, 2},
  {"octa", nds32_aligned_cons, 4},
  {"quad", nds32_aligned_cons, 3},
  {"qword", nds32_aligned_cons, 4},
  {"short", nds32_aligned_cons, 1},
  {"byte", nds32_aligned_cons, 0},
  {"single", nds32_aligned_float_cons, 'f'},
  {"string", stringer, 8 + 1},
  {"word", nds32_aligned_cons, 2},

  {"little", little, 1},
  {"big", little, 0},
  {"restore_16bit", restore_16bit, 0},
  {"off_16bit", off_16bit, 0},

  {"sdata_d", nds32_seg, SDATA_D_SECTION},
  {"sdata_w", nds32_seg, SDATA_W_SECTION},
  {"sdata_h", nds32_seg, SDATA_H_SECTION},
  {"sdata_b", nds32_seg, SDATA_B_SECTION},
  {"sdata_f", nds32_seg, SDATA_F_SECTION},

  {"sbss_d", nds32_seg, SBSS_D_SECTION},
  {"sbss_w", nds32_seg, SBSS_W_SECTION},
  {"sbss_h", nds32_seg, SBSS_H_SECTION},
  {"sbss_b", nds32_seg, SBSS_B_SECTION},
  {"sbss_f", nds32_seg, SBSS_F_SECTION},

  {"pic", nds32_pic, 0},
  {"abi_1", nds32_abi, E_NDS_ABI_V1},
  {"abi_2", nds32_abi, E_NDS_ABI_AABI},
  {"abi_2fp", nds32_abi, E_NDS_ABI_V2FP},
  {"relax", nds32_relax_relocs, 1},
  {"no_relax", nds32_relax_relocs, 0},
  {"hint_func_args", nds32_set_hint_func_args, 0},
  {"omit_fp_begin", nds32_omit_fp_begin, 1},
  {"omit_fp_end", nds32_omit_fp_begin, 0},
  {"no_ex9_begin", nds32_no_ex9_begin, 1},
  {"no_ex9_end", nds32_no_ex9_begin, 0},
  {"vec_size", nds32_vec_size, 0},
  {"flag", nds32_flag, 0},
  {"innermost_loop_begin", nds32_loop_begin, 1},
  {"innermost_loop_end", nds32_loop_begin, 0},
  {NULL, NULL, 0}
};

static void
nds32_insert_align_reloc (int n)
{
  /* Optimize for space and label exists.  */
  fixS *fixP;
  expressionS exp;

  /* COLE: FIXME:
     I think this will break debug info sections and except_table.  */
  if (!enable_relax_relocs || !subseg_text_p (now_seg))
    return;

  /* Create and attach a BFD_RELOC_NDS32_LABEL fixup
     the size of instruction may not be correct because
     it could be relaxable.  */
  exp.X_op = O_symbol;
  exp.X_add_symbol = section_symbol (now_seg);
  exp.X_add_number = 0;
  fixP = fix_new_exp (frag_now,
		      frag_now_fix (), 0, &exp, 0, BFD_RELOC_NDS32_LABEL);
  /* Chain the fixup together.  */
  fixP->tc_fix_data = (fixS*) get_prev_fix ();
  fixP->fx_offset = n;

  set_prev_fix (fixP);
}

void
nds32_pre_do_align (int n, char *fill, int len, int max)
{
  /* Only make a frag if we HAVE to...  */
  if (n != 0 && !need_pass_2)
    {
      if (fill == NULL)
	{
	  if (subseg_text_p (now_seg))
	    frag_align_code (n, max);
	  else
	    frag_align (n, 0, max);
	}
      else if (len <= 1)
	frag_align (n, *fill, max);
      else
	frag_align_pattern (n, fill, len, max);
    }
}

void
nds32_do_align (int n)
{
  nds32_insert_align_reloc (n);
}

/* Supported Andes machines.  */
struct nds32_machs
{
  enum bfd_architecture bfd_mach;
  int mach_flags;
};

/* GAS will call this function at the start of the assembly, after the command
   line arguments have been parsed and all the machine independent
   initializations have been completed.  */

void
md_begin (void)
{
  const builtin_proc_entry *builtin_proc;
  const char *hash_err = NULL;
  nds32_regs *sym;
  int i;

  if (stdoutput != NULL)
    bfd_set_arch_mach (stdoutput, TARGET_ARCH, march_cpu_opt);

  /* Initialize the `cgen' interface.
     Set the machine number and endian.  */
  gas_cgen_cpu_desc = nds32_cgen_cpu_open (CGEN_CPU_OPEN_BFDMACH,
					   bfd_printable_name (stdoutput),
					   CGEN_CPU_OPEN_ENDIAN,
					   (target_big_endian ?
					    CGEN_ENDIAN_BIG : CGEN_ENDIAN_LITTLE),
					   CGEN_CPU_OPEN_END);
  nds32_cgen_init_asm (gas_cgen_cpu_desc);

  /* The operand instance table is used during optimization to determine
     which instructions can be executed in parallel.  It is also used to give
     warnings regarding operand interference in parallel instructions.  */
  nds32_cgen_init_opinst_table (gas_cgen_cpu_desc);

  /* This is a callback from cgen to gas to parse operands.  */
  cgen_set_parse_operand_fn (gas_cgen_cpu_desc, gas_cgen_parse_operand);

  gas_cgen_initialize_saved_fixups_array ();

  /* Only the base substitution table and local label table are initialized;
     the others (for local macro substitution) get instantiated as needed.  */
  local_label_hash[0] = hash_new ();
  builtin_hash[0] = hash_new ();
  for (builtin_proc = builtin_procs; builtin_proc->name; builtin_proc++)
    hash_err = hash_insert (builtin_hash[0], builtin_proc->name,
			    (char *) builtin_proc);
  builtin_recurse_hash = hash_new ();

  reg5_hash = hash_new ();
  reg4_hash = hash_new ();
  reg3_hash = hash_new ();
  for (sym = enable_reduce_regs ? reduce_regs : regs; sym->name; sym++)
    {
      /* Add basic registers to the symbol table.  */
      symbol_table_insert (symbol_new (sym->name, reg_section,
				       (valueT) sym->index,
				       &zero_address_frag));

      if (sym->flag & ADDRESSABLE_5BIT)
	hash_err = hash_insert (reg5_hash, sym->name, (char *) sym);
      if (sym->flag & ADDRESSABLE_4BIT)
	hash_err = hash_insert (reg4_hash, sym->name, (char *) sym);
      if (sym->flag & ADDRESSABLE_3BIT)
	hash_err = hash_insert (reg3_hash, sym->name, (char *) sym);
    }

  nds32_init_nds32_pseudo_opcodes ();

  if (enable_fpu_sp_extension || enable_fpu_dp_extension)
    {
      fs5_hash = hash_new ();
      for (sym = fs_regs, i = 0; i < fs_reg_num; sym++, i++)
	{
	  symbol_table_insert (symbol_new (sym->name, reg_section,
					   (valueT) sym->index,
					   &zero_address_frag));

	  hash_err = hash_insert (fs5_hash, sym->name, (char *) sym);
	}

      fd5_hash = hash_new ();
      for (sym = fd_regs, i = 0; i < fd_reg_num; sym++, i++)
	{
	  /* Add basic registers to the symbol table.  */
	  symbol_table_insert (symbol_new (sym->name, reg_section,
					   (valueT) sym->index,
					   &zero_address_frag));

	  hash_err = hash_insert (fd5_hash, sym->name, (char *) sym);
	}
    }

  if (hash_err)
    as_bad ("Fail to initialize hash table for register "
	    "symbols in md_begin ().  Reason: %s.", hash_err);

  nds32_init_insn_num_map ();

  init_cfg_var ();
}

/* This function counts number of operands in front of subtype.  */

static int
parse_reg_count (char *insn, char **pos)
{
  int n;

  for (*pos = insn, n = 0; *pos != NULL; n++)
    {
      char *tmp;

      while (ISSPACE ((*pos)[0]))
	(*pos)++;
      if (!strncmp (*pos, "$", 1))
	{
	  if ((tmp = strchr (*pos, ',')) == NULL)
	    break;
	  else
	    *pos = tmp + 1;
	}
      else
	{
	  break;
	}
    }

  return n;
}

/* COLE: This should be the responsibility of cgen.  */
/* This function performs special checking on cctl and tlbop instructions.  */

static int
is_cctl_or_tlbop (char *insn)
{
  char *file;			/* filename of current source.  */
  unsigned int line;		/* line number of current source.  */

  /* First idea to fixup bugzilla 1127.
     Since current (Harry@Apr.10.2007) nds32_start_line_hook() grab
     line pointer to local, the line number is wrong.
     Thus, I get current filename ans line number using as_where(),
     then, plus line number by one.
     So, use this workaround for in nds32_start_line_hook() and
     is_cctl_or_tlbop().
     Also we need to use as_bad_where() instead of as_bad().  */
  as_where (&file, &line);
  line += 1;

  while (ISSPACE (insn[0]))
    insn++;

  if (strncasecmp (insn, "cctl", 4) == 0 && ISSPACE (insn[4]))
    {
      /* Check cctl.  */
      int n, i;
      char *pos, *end;
      char *subtype_tbl[] = {
	  "L1D_IX_INVAL", "L1D_IX_WB", "L1D_IX_WBINVAL", "L1D_IX_RTAG",
	  "L1D_IX_RWD", "L1D_IX_WTAG", "L1D_IX_WWD", "L1D_INVALALL",
	  "L1D_VA_INVAL", "L1D_VA_WB", "L1D_VA_WBINVAL", "L1D_VA_FILLCK",
	  "L1D_VA_ULCK", "", "", "L1D_WBALL",
	  "L1I_IX_INVAL", "", "", "L1I_IX_RTAG",
	  "L1I_IX_RWD", "L1I_IX_WTAG", "L1I_IX_WWD", "",
	  "L1I_VA_INVAL", "", "", "L1I_VA_FILLCK",
	  "L1I_VA_ULCK", "", "", "",
      };
      int subtype = -1;
      int level;
      char opline[64] = { 0 };

      for (insn += 5; ISSPACE (insn[0]); insn++)
	/* Skip space.  */ ;

      /* 'pos' pointers to SubType.  */
      n = parse_reg_count (insn, &pos);

      strncpy (opline, pos, sizeof (opline) - 1);
      for (end = opline + strlen (opline) - 1; end > opline; end--)
	if (ISSPACE (*end) || is_end_of_line[(unsigned char) *end])
	  *end = '\0';
	else
	  break;

      /* Convert SubType to numeric value.  */
      subtype = strtol (opline, &end, 10);

      if (*end != '\0' && *end != ',')
	{
	  /* Parse mnemonic string.  */
	  subtype = -1;
	  end = strchr (opline, ',');
	  if (end)
	    *end++ = '\0';
	  else
	    end = strlen (opline) + opline;
	  /* To upper.  */
	  for (pos = opline; *pos; pos++)
	    *pos = TOUPPER (*pos);
	  for (i = 0; i < (int) ARRAY_SIZE (subtype_tbl); i++)
	    if (strcmp (subtype_tbl[i], opline) == 0)
	      subtype = i;
	}
      else if (*end == ',')
	end++;
      pos = end;

      if (subtype == -1)
	as_bad_where (file, line, _("Unknown CCTL subtype field. %s"), insn);

      /* Parse level.  */
      if (!pos)
	/* Default 1level.  */
	level = 0;
      else if (strcmp (pos, "1level") == 0)
	level = 0;
      else if (strcmp (pos, "alevel") == 0)
	level = 1;
      else
	{
	  level = strtol (pos, &end, 10);
	  if (*end != '\0')
	    as_bad_where (file, line, _("Unknown CCTL level field. %s"),
			  insn);
	}
      if (level)
	nds32_flags |= E_NDS32_HAS_L2C_INST;

      /* Check level only for VA write-back or invalidation.  */
      if (level && (((subtype & 8) == 0) || (subtype % 8 >= 3)))
	as_warn_where (file, line,
		       _("CCTL alevel is only allowed for VA write-back "
			 "or invalidate operations. %s\n"), insn);


      /* Check register number.  */
      switch (subtype)
	{
	case 8: case 9: case 24:
	  /* 1 or 2 registers.  */
	  if (n != 1 && n != 2)
	    as_bad_where (file, line,
			  _("Invalid syntax for the specified subtype"));
	  break;
	case 0: case 1: case 16: case 27: case 28:
	  /* 1 register.  */
	  if (n != 1)
	    as_bad_where (file, line,
			  _("Invalid syntax for the specified subtype"));
	  break;
	case 3: case 4: case 5: case 6:
	case 19: case 20: case 21: case 22:
	  /* 2 registers.  */
	  if (n != 2)
	    as_bad_where (file, line,
			  _("Invalid syntax for the specified subtype. %s"),
			  insn);
	  break;
	case 7: case 15:
	  /* 0 registers.  */
	  if (n != 0)
	    as_bad_where (file, line,
			  _("Invalid syntax for the specified subtype. %s"),
			  insn);
	  break;
	default:
	  as_warn_where (file, line, _("Unknow CCTL subtype. %s\n"), insn);
	  break;
	}

      return 1;
    }
  else if (strncasecmp (insn, "tlbop", 5) == 0 && ISSPACE (insn[5]))
    {
      /* Check tlbop.  */
      char *subtype;

      for (insn += 6; ISSPACE (insn[0]); insn++)
	/* Skip white space.  */ ;

      subtype = nds32_strcasestr (insn, "FLUA");
      if (subtype == NULL)
	subtype = nds32_strcasestr (insn, "FlushAll");
      if (subtype != NULL)
	{
	  /* FlushAll or FLUA expects no register.  */
	  if (subtype != insn)
	    as_bad_where (file, line,
			  _("Invalid syntax for the specified subtype"));
	}
      else if (!(insn[0] == '7' && ISSPACE (insn[1])))
	{
	  char *pos;
	  int n = parse_reg_count (insn, &pos);

	  if (ISDIGIT (pos[0]))
	    {
	      int stno = atoi (pos);

	      if ((stno == 5 && n != 2)
		  || (((stno >= 0 && stno <= 4) || stno == 6) && n != 1))
		as_bad_where (file, line,
			      _("Invalid syntax for the specified subtype"));
	    }
	  else
	    {
	      subtype = nds32_strcasestr (pos, "PB");
	      if (subtype == NULL)
		subtype = nds32_strcasestr (pos, "Probe");
	      if ((n != 1 && subtype == NULL) || (n != 2 && subtype != NULL))
		as_bad_where (file, line,
			      _("Invalid syntax for the specified subtype"));
	    }
	}
      return 1;
    }
  else
    return 0;
}

/* md_start_line_hook, used to substitution symbols.
   It hijacks input_line_pointer, replacing it with our
   substituted string and returns the new buffer limit.  */

void
nds32_start_line_hook (void)
{
  char *line, *endp;
  char *replacement = NULL;

  /* Work with a copy of the input line, including EOL char.  */
  endp = input_line_pointer;
  /* Skip line-separate-chars.  E.g., ;, \n.  */
  while (!is_end_of_line[(unsigned char) *endp++])
    ;
  line = xmalloc (endp - input_line_pointer + 1);
  strncpy (line, input_line_pointer, endp - input_line_pointer + 1);
  line[endp - input_line_pointer] = 0;

  /* Need to handle cctl and tlbop specially.  */
  if (!is_cctl_or_tlbop (line))
    {
      /* Within a macro or not?  */
      if (macro_level > 0)
	{
	  /* Yes, first process forced replacements.  */
	  char *tmp = builtin_substitute (line, 1);

	  if (tmp == line)
	    replacement = builtin_substitute (line, 0);
	  else
	    {
	      replacement = builtin_substitute (tmp, 0);
	      if (replacement != tmp)
		free (tmp);
	    }
	}
      else
	/* No.  */
	replacement = builtin_substitute (line, 0);

      if (replacement != line)
	{
	  char *tmp = replacement;
	  char *comment = strpbrk (replacement, comment_chars);
	  char endc = replacement[strlen (replacement) - 1];

	  /* Clean up the replacement; we'd prefer to have this done by the
	     standard preprocessing equipment (maybe do_scrub_chars?)
	     but for now, do a quick-and-dirty.  */
	  if (comment != NULL)
	    {
	      comment[0] = endc;
	      comment[1] = 0;
	      --comment;
	    }
	  else
	    comment = replacement + strlen (replacement) - 1;

	  /* Trim trailing whitespace.  */
	  while (ISSPACE (*comment))
	    {
	      comment[0] = endc;
	      comment[1] = 0;
	      --comment;
	    }

	  /* Compact leading whitespace.  */
	  while (ISSPACE (tmp[0]) && ISSPACE (tmp[1]))
	    ++tmp;

	  /* It is ugly - we need to call bump_line_counters,
	     if it is not macro expansion.  */
	  if (macro_level == 0)
	    bump_line_counters ();

	  input_line_pointer = endp;
	  input_scrub_insert_line (tmp);
	  free (replacement);
	}
    }
  free (line);
}

/* Non-zero if we've seen a relaxable insn since the last 32 bit alignment
   request.  */
static int seen_relaxable_p = 0;

/* Structure to hold all of the different components describing an individual
   instruction.  */

typedef struct
{
  const CGEN_INSN *insn;
  const CGEN_INSN *orig_insn;
  CGEN_FIELDS fields;
#if CGEN_INT_INSN_P
  CGEN_INSN_INT buffer[1];
#define INSN_VALUE(buf) (*(buf))
#else
  unsigned char buffer[CGEN_MAX_INSN_SIZE];
#define INSN_VALUE(buf) (buf)
#endif
  char *addr;
  fragS *frag;
  int num_fixups;
  fixS *fixups[GAS_CGEN_MAX_FIXUPS];
  int indices[MAX_OPERAND_INSTANCES];
} nds32_insn;

/* HANDLE_ALIGN in write.c.  */

void
nds32_handle_align (fragS *fragp)
{
  static const unsigned char nop16[] = { 0x92, 0x00 };
  static const unsigned char nop32[] = { 0x40, 0x00, 0x00, 0x09 };
  int bytes, fix;
  char *p;

  if (fragp->fr_type != rs_align_code)
    return;

  bytes = fragp->fr_next->fr_address - fragp->fr_address - fragp->fr_fix;
  p = fragp->fr_literal + fragp->fr_fix;
  fix = 0;

  if (bytes & 1)
    {
      /* Cannot be in code sections, so pack a 0x00.  */
      *p++ = 0;
      bytes--;
      fix = 1;
    }

  if (bytes & 2)
    {
      /* Can be in any sections, so better pack a 16-bit nop.  */
      expressionS exp_t;
      exp_t.X_op = O_symbol;
      exp_t.X_add_symbol = abs_section_sym;
      exp_t.X_add_number = R_NDS32_INSN16_CONVERT_FLAG;
      fix_new_exp (fragp, fragp->fr_fix, 2, &exp_t, 0,
		   BFD_RELOC_NDS32_INSN16);
      memcpy (p, nop16, 2);
      p += 2;
      bytes -= 2;
      fix += 2;
    }

  /* We need to pack a 32-bit nop.  */
  while (bytes >= 4)
    {
      /* To save the trouble, pack a 32-bit nop.  */
      memcpy (p, nop32, 4);
      p += 4;
      bytes -= 4;
      fix += 4;
    }

  fragp->fr_fix += fix;
  fragp->fr_var = 4;
}

/* md_flush_pending_output  */

void
nds32_flush_pending_output (void)
{
  nds32_last_label = NULL;
}

void
nds32_frob_label (symbolS *label)
{
  struct insn_label_list *insn_label;

  if (optimize && subseg_text_p (now_seg))
    {
      label_exist = 1;
    }

  nds32_last_label = label;

  /* COLE:
     Used for BB analysis for relaxation?
     I think this should be put in nds32_frob_label,
     because it calls this function too and
     tc_frob_label is call once a label is created.  */
  if (bb_now->insn_head != NULL || bb_now->frchain_now != frchain_now)
    create_new_basic_block ();
  insn_label = xmalloc (sizeof (insn_label_list));
  insn_label->label = label;
  insn_label->next = bb_now->label_list;
  bb_now->label_list = insn_label;

  dwarf2_emit_label (label);
}

/* TC_START_LABEL  */

int
nds32_start_label (int asmdone ATTRIBUTE_UNUSED, int secdone ATTRIBUTE_UNUSED)
{
  if (optimize && subseg_text_p (now_seg))
    label_exist = 1;

  return 1;
}

/* TARGET_FORMAT  */

const char *
nds32_target_format (void)
{
#ifdef TE_LINUX
  if (target_big_endian)
    return "elf32-nds32be-linux";
  else
    return "elf32-nds32le-linux";
#else
  if (target_big_endian)
    return "elf32-nds32be";
  else
    return "elf32-nds32le";
#endif
}


/* remove _r of relaxable instruction for display.  */

static char *
rem__r (char *str)
{
  char *tmp = str;

  /* Skip label if any.  */
  while (*str && *str != ':')
    {
      str++;
    }

  if (*str == 0)
    {
      /* No label, start from beginning.  */
      str = tmp;
    }
  else
    {
      /* Label found, skip it.  */
      str++;
    }

  /* Skip white space.  */
  while (*str == ' ' || *str == '\t')
    {
      str++;
    }

  /* Search _r until white space.  */
  while (*str != ' ' && *str != '\t')
    {
      if (*str == '_' && *(str + 1) == 'r')
	{
	  *str = ' ';
	  *(str + 1) = ' ';
	  break;
	}

      str++;
    }

  return tmp;
}

static int
reg_out_of_range (char *str)
{
  char *p;
  int check_one_operand = 0;
  int got_opcode = 0;

  p = alloca (strlen (str) + 1);
  strcpy (p, str);
  p = strtok (p, " ,;+-<>[]");
  while (p)
    {
      if (*p == '$')
	{
	  /* Register found?  */
	  if (!builtin_isreg (p, 0))
	    {
	      /* Invalid register used.  */
	      return 1;
	    }
	  else if (check_one_operand)
	    {
	      return 0;
	    }
	}
      else if (!got_opcode)
	{
	  got_opcode = 1;
	  if (!
	      (strcmp (p, "mfusr") && strcmp (p, "mtusr")
	       && strcmp (p, "mfsr") && strcmp (p, "mtsr")))
	    {
	      check_one_operand = 1;
	    }
	}

      p = strtok (NULL, " ,;+-<>[]");
    }

  return 0;
}

static dep_node *
append_dep_node (dep_node ** node, short reg, short flag)
{
  dep_node *next = xmalloc (sizeof (dep_node));
  next->reg_num = reg;
  next->flag = flag;
  if (*node != NULL)
    {
      next->next = (*node)->next;
      (*node)->next = next;
    }
  else
    {
      next->next = NULL;
      *node = next;
    }
  return next;
}

static void
insert_reg_to_node_list (dep_node ** node_list, short reg, short flag,
			 int merge)
{
  dep_node *node = *node_list, *node2 = NULL;

  while (node != NULL)
    {
      node2 = node;
      if (node->reg_num == reg)
	{
	  if (merge)
	    node->flag |= flag;
	  return;
	}
      node = node->next;
    }

  if (node2 == NULL)
    append_dep_node (node_list, reg, flag);
  else
    append_dep_node (&node2, reg, flag);
}

static void
analysis_regdep (nds32_insn_instant *insn_s, nds32_insn *insn,
		 CGEN_FIELDS *fields, const CGEN_OPINST *oi_p)
{
  const CGEN_OPINST *oi, *oi_bak;
  int i, mask4, type;
  dep_node *gr_dep_list;
  short reg;
  char *reg_name;

  if (CGEN_INSN_NUM (insn->insn) == -1)
    oi = oi_p;
  else
    oi = insn->insn->opinst;
  oi_bak = oi;

  switch (insn_s->insn_num)
    {
    case NDS32_INSN_LMW_BI:
    case NDS32_INSN_LMW_BIM:
    case NDS32_INSN_LMW_BD:
    case NDS32_INSN_LMW_BDM:
    case NDS32_INSN_LMW_AI:
    case NDS32_INSN_LMW_AIM:
    case NDS32_INSN_LMW_AD:
    case NDS32_INSN_LMW_ADM:
    case NDS32_INSN_LMWA_BI:
    case NDS32_INSN_LMWA_BIM:
    case NDS32_INSN_LMWA_BD:
    case NDS32_INSN_LMWA_BDM:
    case NDS32_INSN_LMWA_AI:
    case NDS32_INSN_LMWA_AIM:
    case NDS32_INSN_LMWA_AD:
    case NDS32_INSN_LMWA_ADM:
    case NDS32_INSN_LMWZB_B:
    case NDS32_INSN_LMWZB_BM:
    case NDS32_INSN_LMWZB_A:
    case NDS32_INSN_LMWZB_AM:
      if (insn->insn->
	  base->mnemonic[strlen (insn->insn->base->mnemonic) - 1] == 'm')
	gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			   (short) CGEN_FIELDS_RA5 (*fields),
			   (short) (CGEN_OPINST_INPUT_MASK
				    | CGEN_OPINST_OUTPUT_MASK));
      else
	gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			   (short) CGEN_FIELDS_RA5 (*fields),
			   (short) CGEN_OPINST_INPUT_MASK);
      for (i = CGEN_FIELDS_RT5 (*fields); i <= CGEN_FIELDS_RB5 (*fields); i++)
	{
	  gr_dep_list = append_dep_node (&gr_dep_list, (short) i,
			     (short) CGEN_OPINST_OUTPUT_MASK);
	}
      mask4 = CGEN_FIELDS_MASK4 (*fields);
      for (i = 28; i < 32; i++)
	{
	  if ((mask4 & 0x1000) > 0)
	    {
	      gr_dep_list = append_dep_node (&gr_dep_list, (short) i,
				 (short) CGEN_OPINST_OUTPUT_MASK);
	    }
	  mask4 = mask4 << 1;
	}
      return;
    case NDS32_INSN_SMW_BI:
    case NDS32_INSN_SMW_BIM:
    case NDS32_INSN_SMW_BD:
    case NDS32_INSN_SMW_BDM:
    case NDS32_INSN_SMW_AI:
    case NDS32_INSN_SMW_AIM:
    case NDS32_INSN_SMW_AD:
    case NDS32_INSN_SMW_ADM:
    case NDS32_INSN_SMWA_BI:
    case NDS32_INSN_SMWA_BIM:
    case NDS32_INSN_SMWA_BD:
    case NDS32_INSN_SMWA_BDM:
    case NDS32_INSN_SMWA_AI:
    case NDS32_INSN_SMWA_AIM:
    case NDS32_INSN_SMWA_AD:
    case NDS32_INSN_SMWA_ADM:
    case NDS32_INSN_SMWZB_B:
    case NDS32_INSN_SMWZB_BM:
    case NDS32_INSN_SMWZB_A:
    case NDS32_INSN_SMWZB_AM:
      if (insn->insn->
	  base->mnemonic[strlen (insn->insn->base->mnemonic) - 1] == 'm')
	gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			   (short) CGEN_FIELDS_RA5 (*fields),
			   (short) (CGEN_OPINST_INPUT_MASK
				    | CGEN_OPINST_OUTPUT_MASK));
      else
	gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			   (short) CGEN_FIELDS_RA5 (*fields),
			   (short) CGEN_OPINST_INPUT_MASK);
      for (i = CGEN_FIELDS_RT5 (*fields); i <= CGEN_FIELDS_RB5 (*fields); i++)
	{
	  gr_dep_list = append_dep_node (&gr_dep_list, (short) i,
			     (short) CGEN_OPINST_INPUT_MASK);
	}
      mask4 = CGEN_FIELDS_MASK4 (*fields);
      for (i = 28; i < 32; i++)
	{
	  if ((mask4 & 0x1000) > 0)
	    {
	      gr_dep_list = append_dep_node (&gr_dep_list, (short) i,
				 (short) CGEN_OPINST_INPUT_MASK);
	    }
	  mask4 = mask4 << 1;
	}
      return;
    case NDS32_INSN_SYSCALL:
      gr_dep_list = append_dep_node (&insn_s->gr_dep_list, (short) 0,
			 (short) (CGEN_OPINST_INPUT_MASK
				  | CGEN_OPINST_OUTPUT_MASK));
      for (i = 1; i <= 5; i++)
	{
	  gr_dep_list = append_dep_node (&gr_dep_list, (short) i,
			     (short) CGEN_OPINST_INPUT_MASK);
	}
      return;
    /* Coprocessor instruction set.  */
    case NDS32_INSN_MFCPW_CP1:
    case NDS32_INSN_MFCPW_CP2:
    case NDS32_INSN_MFCPW_CP3:
      gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			 (short) CGEN_FIELDS_RT5 (*fields),
			 (short) (CGEN_OPINST_OUTPUT_MASK));
      return;
    case NDS32_INSN_BSE:
    case NDS32_INSN_BSP:
      gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			 (short) CGEN_FIELDS_RT5 (*fields),
			 (short) (CGEN_OPINST_INPUT_MASK
				  | CGEN_OPINST_OUTPUT_MASK));
      gr_dep_list = append_dep_node (&gr_dep_list,
			 (short) CGEN_FIELDS_RT5 (*fields),
			 (short) CGEN_OPINST_OUTPUT_MASK);
      gr_dep_list = append_dep_node (&gr_dep_list,
			 (short) CGEN_FIELDS_RA5 (*fields),
			 (short) CGEN_OPINST_INPUT_MASK);
      gr_dep_list = append_dep_node (&gr_dep_list,
			 (short) CGEN_FIELDS_RB5 (*fields),
			 (short) (CGEN_OPINST_INPUT_MASK
				  | CGEN_OPINST_OUTPUT_MASK));
      return;

    case NDS32_INSN_FMFSR:
    case NDS32_INSN_FMFDR:
      gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			 (short) CGEN_FIELDS_RT5 (*fields),
			 (short) CGEN_OPINST_OUTPUT_MASK);
      return;
    case NDS32_INSN_MOVD44:
      /* See CGEN_OPINST sfmt_movd44_ops in opcode/nds32-opinst.c.  */
      gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			 (short) CGEN_FIELDS_RT5E (*fields) * 2,
			 (short) CGEN_OPINST_OUTPUT_MASK);
      gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			 (short) CGEN_FIELDS_RT5E (*fields) * 2 + 1,
			 (short) CGEN_OPINST_OUTPUT_MASK);
      gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			 (short) CGEN_FIELDS_RA5E (*fields) * 2,
			 (short) CGEN_OPINST_INPUT_MASK);
      gr_dep_list = append_dep_node (&insn_s->gr_dep_list,
			 (short) CGEN_FIELDS_RA5E (*fields) * 2 + 1,
			 (short) CGEN_OPINST_INPUT_MASK);
      return;
    default:
      ;
    }

  for (reg = -1; oi->type != CGEN_OPINST_END; oi++, reg = -1)
    {
      gr_dep_list = insn_s->gr_dep_list;
      switch (oi->hw_type)
	{
	case HW_H_GR:
	case HW_H_GR16:
	case HW_H_GR8:
	case HW_H_GR8E5:
	case HW_H_GR_EVEN:
	case HW_H_GR_ODD:
	case HW_H_GR_LO:
	case HW_H_GR_LO_EVEN:
	case HW_H_GR_LO_ODD:
	case HW_H_GR_BOTTOM:
	case HW_H_GR_TOP:
	case HW_H_GR_LO_BOTTOM:
	case HW_H_GR_LO_TOP:
	  if (!oi->op_type)
	    {
	      if (oi->index)
		reg = oi->index;
	      else
		{
		  reg_name = (char *) (oi->name + strlen (oi->name) - 2);
		  if (strcmp (reg_name, "FP") == 0)
		    reg = 28;
		  else if (strcmp (reg_name, "GP") == 0)
		    reg = 29;
		  else if (strcmp (reg_name, "LP") == 0)
		    reg = 30;
		  else if (strcmp (reg_name, "SP") == 0)
		    reg = 31;
		}
	    }
	  else
	    reg = nds32_cgen_get_int_operand (gas_cgen_cpu_desc, oi->op_type,
					  fields);
	  break;
	default:
	  break;
	}

      if (reg < 0 || reg > 31)
	continue;

      if (oi->type == CGEN_OPINST_INPUT)
	insert_reg_to_node_list (&insn_s->gr_dep_list, reg,
				 (short) CGEN_OPINST_INPUT_MASK, TRUE);
      else if (oi->type == CGEN_OPINST_OUTPUT)
	insert_reg_to_node_list (&insn_s->gr_dep_list, reg,
				 (short) CGEN_OPINST_OUTPUT_MASK, TRUE);
    }

  for (oi = oi_bak, type = 0, reg = -1; oi->type != CGEN_OPINST_END;
       oi++, type = 0, reg = -1)
    {
      gr_dep_list = insn_s->gr_dep_list;
      switch (oi->hw_type)
	{
	case HW_H_UINT:
	  if (strncmp (oi->name, "f_32_r", 6) == 0)
	    {
	      /* Insn->insn->opcode->syntax.syntax[1].  */
	      if (strncmp (oi->name + 6, "t5", 2) == 0)
		{
		  for (i = 0; insn->insn->opcode->syntax.syntax[i] != 0; i++)
		    if ((CGEN_SYNTAX_CHAR_P
			 (insn->insn->opcode->syntax.syntax[i]) == 0)
			&& (insn->insn->opcode->syntax.syntax[i]
			   == CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RT5)
			   || (insn->insn->opcode->syntax.syntax[i]
			       == CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RT5H))))
		      break;
		}
	      else if (strncmp (oi->name + 6, "a5", 2) == 0)
		{
		  for (i = 0; insn->insn->opcode->syntax.syntax[i] != 0; i++)
		    if ((CGEN_SYNTAX_CHAR_P
			 (insn->insn->opcode->syntax.syntax[i]) == 0)
			&& (insn->insn->opcode->syntax.syntax[i]
			    == CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RA5)
			    || (insn->insn->opcode->syntax.syntax[i]
				== CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RA5H))
			    || (insn->insn->opcode->syntax.syntax[i]
				>= CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RA5_A)
				&& insn->insn->opcode->syntax.syntax[i]
				   <= CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RA5_A_T))))
		      break;

		  /* For FPU & COProcessor load/store with .bi form.
		     The definitions in the nds32-opinst only indicate $ra is
		     an input for these instructions.
		     Following process is used to detect if current instruction
		     is in .bi form.
		     This method is a little tricky since there is too much
		     instructions with .bi form, and it is hard to detect them
		     use switch table or sequential if/else checking.  */
		  if (oi == gas_cgen_cpu_desc->insn_table.init_entries[NDS32_INSN_FLS].opinst
		      || oi == gas_cgen_cpu_desc->insn_table.init_entries[NDS32_INSN_FLSI].opinst
		      || oi == gas_cgen_cpu_desc->insn_table.init_entries[NDS32_INSN_FLDI].opinst)
		    {
		      if (strcmp ((insn->insn->base->mnemonic
				   + strlen (insn->insn->base->mnemonic) - 3),
				  ".bi"))
			type |= CGEN_OPINST_OUTPUT_MASK;
		    }
		}
	      else if (strncmp (oi->name + 6, "b5", 2) == 0)
		{
		  for (i = 0; insn->insn->opcode->syntax.syntax[i] != 0; i++)
		    if ((CGEN_SYNTAX_CHAR_P
			 (insn->insn->opcode->syntax.syntax[i] == 0))
			&& (insn->insn->opcode->syntax.syntax[i]
			    == CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RB5)
			    || (insn->insn->opcode->syntax.syntax[i]
				== CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RB5H))
			    || (insn->insn->opcode->syntax.syntax[i]
				>= CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RB5_A)
				&& insn->insn->opcode->syntax.syntax[i]
				   <= CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RB5P_A_T))))
		      break;
		}
	      else if (strncmp (oi->name + 6, "s5", 2) == 0)
		{
		  for (i = 0; insn->insn->opcode->syntax.syntax[i] != 0; i++)
		    if (insn->insn->opcode->syntax.syntax[i]
			== CGEN_SYNTAX_MAKE_FIELD (NDS32_OPERAND_RS5))
		      break;
		}
	      else
		break;

	      if (insn->insn->opcode->syntax.syntax[i])
		reg = nds32_cgen_get_int_operand
		  (gas_cgen_cpu_desc,
		   CGEN_SYNTAX_FIELD (insn->insn->opcode->syntax.syntax[i]),
				      fields);
	    }
	  break;

	default:
	  break;
	}

      if (reg < 0 || reg > 31)
	continue;

      if (oi->type == CGEN_OPINST_INPUT)
	type |= CGEN_OPINST_INPUT;
      else if (oi->type == CGEN_OPINST_OUTPUT)
	type |= CGEN_OPINST_OUTPUT;
      insert_reg_to_node_list (&insn_s->gr_dep_list, reg, (short) type,
			       FALSE);
    }
}

static void
assign_instant (nds32_insn_instant *insn_s, int insn_num,
		finished_insnS *fi, short insn_szp, short byte_szp,
		nds32_insn *insn, int relaxable, const CGEN_OPINST *oi)
{
  int i;
  CGEN_FIELDS *fields = &insn->fields;
  insn_s->insn_num = insn_num;
  insn_s->addr = fi->addr;
  insn_s->frag = fi->frag;
  insn_s->num_fixups = fi->num_fixups;
  insn_s->byte_sz = byte_szp;
  insn_s->insn_sz = insn_szp;
  insn_s->gr_dep_list = NULL;
  insn_s->parent = bb_now;
  insn_s->md_relax = relaxable;
  if (is_func_branch (insn_num) == IS_FUNC_CALL_MASK
      || is_func_branch (insn_num) == IS_COND_FUNC_CALL_MASK)
    {
      insn_s->hint_func_args = hint_func_args;
      hint_func_args = 0;
    }
  insn_s->reloc_node = NULL;
  for (i = 0; i < insn_s->num_fixups; i++)
    insn_s->fixups[i] = fi->fixups[i];
  if (insn_num > NDS32_INSN_INVALID && insn_num < MAX_INSNS)
    analysis_regdep (insn_s, insn, fields, oi);
  if (prev_insn_s != NULL)
    prev_insn_s->next = insn_s;
  insn_s->prev = prev_insn_s;
  insn_s->next = NULL;
  prev_insn_s = insn_s;
}

/* Since the nds32_cgen_macro_insn_table always provide insn_num as -1,
   it is impossible to get real insn_num of an alias instruction.  */

static int
convert_macro_insn_to_insn (nds32_insn *pinsn, const CGEN_OPINST ** oi)
{
  int insn_num = NDS32_INSN_INVALID;
  CGEN_FIELDS *fields = &pinsn->fields;
  uint32_t insn;

  if (CGEN_INSN_NUM (pinsn->insn) != -1)
    return CGEN_INSN_NUM (pinsn->insn);

  insn = INSN_VALUE (pinsn->buffer);
  if (CGEN_INSN_BITSIZE (pinsn->insn) == 32)
    {
      switch (N32_OP6 (insn))
	{
	case N32_OP6_LBI:
	  insn_num = NDS32_INSN_LBI;
	  break;
	case N32_OP6_LHI:
	  insn_num = NDS32_INSN_LHI;
	  break;
	case N32_OP6_LWI:
	  insn_num = NDS32_INSN_LWI;
	  break;
	case N32_OP6_LBI_BI:
	  insn_num = NDS32_INSN_LBI_BI;
	  break;
	case N32_OP6_LHI_BI:
	  insn_num = NDS32_INSN_LHI_BI;
	  break;
	case N32_OP6_LWI_BI:
	  insn_num = NDS32_INSN_LWI_BI;
	  break;
	case N32_OP6_SBI:
	  insn_num = NDS32_INSN_SBI;
	  break;
	case N32_OP6_SHI:
	  insn_num = NDS32_INSN_SHI;
	  break;
	case N32_OP6_SWI:
	  insn_num = NDS32_INSN_SWI;
	  break;
	case N32_OP6_SBI_BI:
	  insn_num = NDS32_INSN_SBI_BI;
	  break;
	case N32_OP6_SHI_BI:
	  insn_num = NDS32_INSN_SHI_BI;
	  break;
	case N32_OP6_SWI_BI:
	  insn_num = NDS32_INSN_SWI_BI;
	  break;
	case N32_OP6_DPREFI:
	  if (insn & 0x1000000)
	    insn_num = NDS32_INSN_DPREFI_D;
	  else
	    insn_num = NDS32_INSN_DPREFI_W;
	  break;
	case N32_OP6_LWC:
	  if ((insn & 0x6000) == 0)
	    {
	      /* CP0  */
	      if (insn & 0x1000)
		insn_num = NDS32_INSN_FLSI_BI;
	      else
		insn_num = NDS32_INSN_FLSI;
	    }
	  else
	    insn_num = 0;
	  break;
	case N32_OP6_LDC:
	  if ((insn & 0x6000) == 0)
	    {
	      if (insn & 0x1000)
		insn_num = NDS32_INSN_FLDI_BI;
	      else
		insn_num = NDS32_INSN_FLDI;
	    }
	  else
	    insn_num = 0;
	  break;
	case N32_OP6_MEM:		/* Load and store.  */
	  switch (insn & 0xff)
	    {
	    case N32_MEM_LB:
	      insn_num = NDS32_INSN_LB;
	      break;
	    case N32_MEM_LH:
	      insn_num = NDS32_INSN_LH;
	      break;
	    case N32_MEM_LW:
	      insn_num = NDS32_INSN_LW;
	      break;
	    case N32_MEM_LB_BI:
	      insn_num = NDS32_INSN_LB_BI;
	      break;
	    case N32_MEM_LH_BI:
	      insn_num = NDS32_INSN_LH_BI;
	      break;
	    case N32_MEM_LW_BI:
	      insn_num = NDS32_INSN_LW_BI;
	      break;
	    case N32_MEM_SB:
	      insn_num = NDS32_INSN_SB;
	      break;
	    case N32_MEM_SH:
	      insn_num = NDS32_INSN_SH;
	      break;
	    case N32_MEM_SW:
	      insn_num = NDS32_INSN_SW;
	      break;
	    case N32_MEM_SB_BI:
	      insn_num = NDS32_INSN_SB_BI;
	      break;
	    case N32_MEM_SH_BI:
	      insn_num = NDS32_INSN_SH_BI;
	      break;
	    case N32_MEM_SW_BI:
	      insn_num = NDS32_INSN_SW_BI;
	      break;
	    case N32_MEM_LBS:
	      insn_num = NDS32_INSN_LBS;
	      break;
	    case N32_MEM_LHS:
	      insn_num = NDS32_INSN_LHS;
	      break;
	    case N32_MEM_DPREF:
	      insn_num = NDS32_INSN_DPREF;
	      break;
	    case N32_MEM_LBS_BI:
	      insn_num = NDS32_INSN_LBS_BI;
	      break;
	    case N32_MEM_LHS_BI:
	      insn_num = NDS32_INSN_LHS_BI;
	      break;
	    case N32_MEM_LLW:
	      insn_num = NDS32_INSN_LLW;
	      break;
	    case N32_MEM_SCW:
	      insn_num = NDS32_INSN_SCW;
	      break;
	    case N32_MEM_LWUP:
	      insn_num = NDS32_INSN_LWUP;
	      break;
	    case N32_MEM_SWUP:
	      insn_num = NDS32_INSN_SWUP;
	      break;
	    default:
	      insn_num = 0;
	      break;
	    }
	  /* Trick.  COLE: For what?  */
	  fields->f_32_rb5 = N32_RB5 (insn);
	  break;
	case N32_OP6_LSMW:
	  if ((insn & 0x3) == 0)
	    {
	      if ((insn & 0x20) == 0)
		{
		  /* LMW  */
		  switch ((insn >> 2) & 0x7)
		    {
		    case N32_LSMW_BI: /* bi */
		      insn_num = NDS32_INSN_LMW_BI;
		      break;
		    case N32_LSMW_BIM: /* bim */
		      insn_num = NDS32_INSN_LMW_BIM;
		      break;
		    case N32_LSMW_BD: /* bd */
		      insn_num = NDS32_INSN_LMW_BD;
		      break;
		    case N32_LSMW_BDM: /* bdm */
		      insn_num = NDS32_INSN_LMW_BDM;
		      break;
		    case N32_LSMW_AI: /* ai */
		      insn_num = NDS32_INSN_LMW_AI;
		      break;
		    case N32_LSMW_AIM: /* aim */
		      insn_num = NDS32_INSN_LMW_AIM;
		      break;
		    case N32_LSMW_AD: /* ad */
		      insn_num = NDS32_INSN_LMW_AD;
		      break;
		    case N32_LSMW_ADM: /* adm */
		      insn_num = NDS32_INSN_LMW_ADM;
		      break;
		    }
		}
	      else
		{
		  /* SMW */
		  switch ((insn >> 2) & 0x7)
		    {
		    case N32_LSMW_BI: /* bi */
		      insn_num = NDS32_INSN_SMW_BI;
		      break;
		    case N32_LSMW_BIM: /* bim */
		      insn_num = NDS32_INSN_SMW_BIM;
		      break;
		    case N32_LSMW_BD: /* bd */
		      insn_num = NDS32_INSN_SMW_BD;
		      break;
		    case N32_LSMW_BDM: /* bdm */
		      insn_num = NDS32_INSN_SMW_BDM;
		      break;
		    case N32_LSMW_AI: /* ai */
		      insn_num = NDS32_INSN_SMW_AI;
		      break;
		    case N32_LSMW_AIM: /* aim */
		      insn_num = NDS32_INSN_SMW_AIM;
		      break;
		    case N32_LSMW_AD: /* ad */
		      insn_num = NDS32_INSN_SMW_AD;
		      break;
		    case N32_LSMW_ADM: /* adm */
		      insn_num = NDS32_INSN_SMW_ADM;
		      break;
		    }
		}
	    }
	  else if ((insn & 0x3) == 1)
	    {
	      if ((insn & 0x20) == 0)
		{
		  /* LMWA  */
		  switch ((insn >> 2) & 0x7)
		    {
		    case N32_LSMW_BI: /* bi */
		      insn_num = NDS32_INSN_LMWA_BI;
		      break;
		    case N32_LSMW_BIM: /* bim */
		      insn_num = NDS32_INSN_LMWA_BIM;
		      break;
		    case N32_LSMW_BD: /* bd */
		      insn_num = NDS32_INSN_LMWA_BD;
		      break;
		    case N32_LSMW_BDM: /* bdm */
		      insn_num = NDS32_INSN_LMWA_BDM;
		      break;
		    case N32_LSMW_AI: /* ai */
		      insn_num = NDS32_INSN_LMWA_AI;
		      break;
		    case N32_LSMW_AIM: /* aim */
		      insn_num = NDS32_INSN_LMWA_AIM;
		      break;
		    case N32_LSMW_AD: /* ad */
		      insn_num = NDS32_INSN_LMWA_AD;
		      break;
		    case N32_LSMW_ADM: /* adm */
		      insn_num = NDS32_INSN_LMWA_ADM;
		      break;
		    }
		}
	      else
		{
		  /* SMWA */
		  switch ((insn >> 2) & 0x7)
		    {
		    case N32_LSMW_BI: /* bi */
		      insn_num = NDS32_INSN_SMWA_BI;
		      break;
		    case N32_LSMW_BIM: /* bim */
		      insn_num = NDS32_INSN_SMWA_BIM;
		      break;
		    case N32_LSMW_BD: /* bd */
		      insn_num = NDS32_INSN_SMWA_BD;
		      break;
		    case N32_LSMW_BDM: /* bdm */
		      insn_num = NDS32_INSN_SMWA_BDM;
		      break;
		    case N32_LSMW_AI: /* ai */
		      insn_num = NDS32_INSN_SMWA_AI;
		      break;
		    case N32_LSMW_AIM: /* aim */
		      insn_num = NDS32_INSN_SMWA_AIM;
		      break;
		    case N32_LSMW_AD: /* ad */
		      insn_num = NDS32_INSN_SMWA_AD;
		      break;
		    case N32_LSMW_ADM: /* adm */
		      insn_num = NDS32_INSN_SMWA_ADM;
		      break;
		    }
		}
	    }
	  else
	    insn_num = 0;
	  break;
	case N32_OP6_JI:
	  insn_num = insn & 0x1000000 ? NDS32_INSN_JAL :
	    NDS32_INSN_J;
	  break;
	case N32_OP6_JREG:
	  if ((insn & 0x1f) == 1)
	    {
	      /* JRAL, JRAL.ITON, JRAL.TON  */
	      switch ((insn >> 8) & 0x3)
		{
		case 0:
		  insn_num = NDS32_INSN_JRAL;
		  break;
		case 1:
		  insn_num = NDS32_INSN_JRAL_ITON;
		  break;
		case 2:
		  insn_num = NDS32_INSN_JRAL_TON;
		  break;
		default:
		  insn_num = 0;
		  break;
		}
	    }
	  else if ((insn & 0x3f) == 0x20)
	    {
	      /* RET, RET.ITOFF, RET.TOFF  */
	      switch ((insn >> 8) & 0x3)
		{
		case 0:
		  insn_num = NDS32_INSN_RET;
		  break;
		case 1:
		  insn_num = NDS32_INSN_RET_ITOFF;
		  break;
		case 2:
		  insn_num = NDS32_INSN_RET_TOFF;
		  break;
		default:
		  insn_num = 0;
		  break;
		}
	      fields->f_32_rb5 = N32_RB5 (insn);
	    }
	  else
	    insn_num = 0;
	  break;
	case N32_OP6_BR1:
	  insn_num = (insn & 0x4000) ? NDS32_INSN_BNE :
	    NDS32_INSN_BEQ;
	  break;
	case N32_OP6_BR2:
	  switch (((insn & 0xf0000) >> 16) & 0xf)
	    {
	    case N32_BR2_BEQZ:
	      insn_num = NDS32_INSN_BEQZ;
	      break;
	    case N32_BR2_BNEZ:
	      insn_num = NDS32_INSN_BNEZ;
	      break;
	    case N32_BR2_BGEZ:
	      insn_num = NDS32_INSN_BGEZ;
	      break;
	    case N32_BR2_BLTZ:
	      insn_num = NDS32_INSN_BLTZ;
	      break;
	    case N32_BR2_BGTZ:
	      insn_num = NDS32_INSN_BGTZ;
	      break;
	    case N32_BR2_BLEZ:
	      insn_num = NDS32_INSN_BLEZ;
	      break;
	    case N32_BR2_BGEZAL:
	      insn_num = NDS32_INSN_BGEZAL;
	      break;
	    case N32_BR2_BLTZAL:
	      insn_num = NDS32_INSN_BLTZAL;
	      break;
	    default:
	      insn_num = 0;
	      break;
	    }
	  break;
	case N32_OP6_BR3:
	  if ((insn & 0x00080000) == 0x0)
	    insn_num = NDS32_INSN_BEQC;
	  else if ((insn & 0x00080000) == 0x00080000)
	    insn_num = NDS32_INSN_BNEC;
	  else
	    insn_num = 0;
	  break;
	case N32_OP6_SUBRI:
	  insn_num = NDS32_INSN_SUBRI;
	  break;
	case N32_OP6_ANDI:
	  insn_num = NDS32_INSN_ANDI;
	  break;
	case N32_OP6_ALU1:
	  switch (insn & 0x1f)
	    {
	    case N32_ALU1_SRLI:
	      insn_num = NDS32_INSN_SRLI;
	      fields->f_32_rt5 = N32_RT5 (insn);
	      fields->f_32_ra5 = N32_RA5 (insn);
	      break;
	    default:
	      insn_num = 0;
	      break;
	    }
	  break;
	case N32_OP6_ALU2:
	  switch (insn & 0x1f)
	    {
	    case N32_ALU2_BSE:
	      insn_num = NDS32_INSN_BSE;
	      break;
	    case N32_ALU2_BSP:
	      insn_num = NDS32_INSN_BSP;
	      break;
	    default:
	      insn_num = 0;
	      break;
	    }
	  break;
	case N32_OP6_MISC:
	  switch (insn & 0x1f)
	    {
	    case N32_MISC_CCTL:
	      insn_num = NDS32_INSN_CCTL;
	      fields->f_32_rt5 = N32_RT5 (insn);
	      fields->f_32_ra5 = N32_RA5 (insn);
	      break;
	    case N32_MISC_TRAP:
	      insn_num = NDS32_INSN_TRAP;
	      break;
	    case N32_MISC_TEQZ:
	      insn_num = NDS32_INSN_TEQZ;
	      break;
	    case N32_MISC_TNEZ:
	      insn_num = NDS32_INSN_TNEZ;
	      break;
	    case N32_MISC_BREAK:
	      insn_num = NDS32_INSN_BREAK;
	      break;
	    case N32_MISC_MSYNC:
	      insn_num = NDS32_INSN_MSYNC;
	      break;
	    case N32_MISC_TLBOP:
	      insn_num = NDS32_INSN_TLBOP;
	      fields->f_32_rt5 = N32_RT5 (insn);
	      fields->f_32_ra5 = N32_RA5 (insn);
	      break;
	    default:
	      insn = 0;
	      break;
	    }
	  break;
	case N32_OP6_COP:
	  if (((insn >> 4) & 3) == 0)
	    switch (insn & 0xf)
	      {
	      case N32_FPU_FLS:
		if (insn & 0x80)
		  insn_num = NDS32_INSN_FLS_BI;
		else
		  insn_num = NDS32_INSN_FLS;
		break;
	      case N32_FPU_FSS:
		if (insn & 0x80)
		  insn_num = NDS32_INSN_FSS_BI;
		else
		  insn_num = NDS32_INSN_FSS;
		break;
	      case N32_FPU_FLD:
		if (insn & 0x80)
		  insn_num = NDS32_INSN_FLD_BI;
		else
		  insn_num = NDS32_INSN_FLD;
		break;
	      case N32_FPU_FSD:
		if (insn & 0x80)
		  insn_num = NDS32_INSN_FSD_BI;
		else
		  insn_num = NDS32_INSN_FSD;
		break;
	      default:
		insn_num = 0;
		break;
	      }
	  else
	    insn_num = 0;
	  break;
	default:
	  break;
	}
    }
  else
    {
      switch ((insn & 0xf800) >> 11)
	{
	case 0x10:
	  /* 0x8000  */
	  if ((insn & 0x7ff) == 0x3ff)
	    {
	      /* FIXME: ??  */
	      insn_num = NDS32_INSN_IFRET;
	    }
	  break;
	case 0x12:
	  /* 0x9000  */
	  if (((insn >> 9) & 3) == 1)
	    {
	      insn_num = NDS32_INSN_SRLI45;
	      fields->f_16_rt4 = ((insn & 0x01e0) >> 5) & 0xf;
	    }
	  else
	    insn_num = 0;
	  break;
	case 0x14:
	  /* 0xa000  */
	  switch ((insn >> 9) & 3)
	    {
	    case 0x00:
	      insn_num = NDS32_INSN_LWI333;
	      fields->f_16_ra3 = ((insn & 0x0038) >> 3) & 0x7;
	      fields->f_16_rt3_7 = ((insn & 0x01c0) >> 6) & 0x7;
	      break;
	    case 0x02:
	      insn_num = NDS32_INSN_LHI333;
	      fields->f_16_ra3 = ((insn & 0x0038) >> 3) & 0x7;
	      fields->f_16_rt3_7 = ((insn & 0x01c0) >> 6) & 0x7;
	      break;
	    case 0x03:
	      insn_num = NDS32_INSN_LBI333;
	      fields->f_16_ra3 = ((insn & 0x0038) >> 3) & 0x7;
	      fields->f_16_rt3_7 = ((insn & 0x01c0) >> 6) & 0x7;
	      break;
	    default:
	      insn_num = 0;
	      break;
	    }
	  break;
	case 0x15:
	  /* 0xa800  */
	  switch ((insn >> 9) & 3)
	    {
	    case 0x00:
	      insn_num = NDS32_INSN_SWI333;
	      fields->f_16_ra3 = ((insn & 0x0038) >> 3) & 0x7;
	      fields->f_16_rt3_7 = ((insn & 0x01c0) >> 6) & 0x7;
	      break;
	    case 0x02:
	      insn_num = NDS32_INSN_SHI333;
	      fields->f_16_ra3 = ((insn & 0x0038) >> 3) & 0x7;
	      fields->f_16_rt3_7 = ((insn & 0x01c0) >> 6) & 0x7;
	      break;
	    case 0x03:
	      insn_num = NDS32_INSN_SBI333;
	      fields->f_16_ra3 = ((insn & 0x0038) >> 3) & 0x7;
	      fields->f_16_rt3_7 = ((insn & 0x01c0) >> 6) & 0x7;
	      break;
	    default:
	      insn_num = 0;
	      break;
	    }
	  break;
	case 0x17:
	  /* 0xb800  */
	  if (insn & 0x80)
	    insn_num = NDS32_INSN_LWI37;
	  else
	    insn_num = NDS32_INSN_SWI37;
	  fields->f_16_rt3 = ((insn & 0x0700) >> 8) & 0x7;
	  break;
	case 0x18:
	  /* 0xc000  */
	  insn_num = NDS32_INSN_BEQZ38;
	  fields->f_16_rt3 = ((insn & 0x0700) >> 8) & 0x7;
	  break;
	case 0x19:
	  /* 0xc800  */
	  insn_num = NDS32_INSN_BNEZ38;
	  fields->f_16_rt3 = ((insn & 0x0700) >> 8) & 0x7;
	  break;
	case 0x1a:
	  /* 0xd000  */
	  if ((insn & 0x0700) != 0x0500)
	    {
	      insn_num = NDS32_INSN_BEQS38;
	      fields->f_16_rt3 = ((insn & 0x0700) >> 8) & 0x7;
	    }
	  else
	    {
	      insn_num = NDS32_INSN_J8;
	    }
	  break;
	case 0x1b:
	  /* 0xd800  */
	  if ((insn & 0x0700) != 0x0500)
	    {
	      insn_num = NDS32_INSN_BNES38;
	      fields->f_16_rt3 = ((insn & 0x0700) >> 8) & 0x7;
	    }
	  else if ((insn & 0x00e0) == 0x20)
	    {
	      insn_num = NDS32_INSN_JRAL5;
	      fields->f_16_rb5h = insn & 0x1f;
	    }
	  else if ((insn & 0x00e0) == 0x80)
	    {
	      insn_num = NDS32_INSN_RET5;
	      fields->f_16_rb5h = insn & 0x1f;
	    }
	  else
	    {
	      insn_num = 0;
	    }
	  break;
	case 0x1d:
	  /* 0xe800  */
	  if ((insn & 0x0700) == 0x0)
	    {
	      insn_num = NDS32_INSN_BEQZS8;
	    }
	  else if ((insn & 0x0700) == 0x100)
	    {
	      insn_num = NDS32_INSN_BNEZS8;
	    }
	  else
	    {
	      insn_num = 0;
	    }
	  break;
	default:
	  insn_num = 0;
	  break;
	}
    }
  *oi = gas_cgen_cpu_desc->insn_table.init_entries[insn_num].opinst;
  return insn_num;
}

typedef struct seg_fixup seg_fixup;
struct seg_fixup
{
  segT seg;
  fixS *fix;
  seg_fixup *next;
};

static seg_fixup *sf_list = NULL;

static void
set_prev_fix (fixS *fix_p)
{
  seg_fixup *sf_t = sf_list;

  while (sf_t)
    {
      if (sf_t->seg == now_seg)
	break;
      sf_t = sf_t->next;
    }
  if (!sf_t)
    {
      sf_t = xmalloc (sizeof (seg_fixup));
      sf_t->next = sf_list;
      sf_list = sf_t;
    }
  sf_t->seg = now_seg;
  sf_t->fix = fix_p;
}

static fixS *
get_prev_fix (void)
{
  seg_fixup *sf_t = sf_list;

  while (sf_t)
    {
      if (sf_t->seg == now_seg)
	break;
      sf_t = sf_t->next;
    }
  if (sf_t)
    return sf_t->fix;
  return NULL;
}

static void
clean_seg_fixup_list (void)
{
  seg_fixup *sf_t;

  while (sf_list)
    {
      sf_t = sf_list->next;
      free (sf_list);
      sf_list = sf_t;
    }
}

/* This function is used to create new fixups with LABEL relocations and append
   them to the newest fragment(may or may not be frag_now).  */
static void
append_label_reloc (fragS *frag, int byte_sz_p)
{
  /* Optimize for space and label exists.  */
  fixS *fixP;
  expressionS exp;
  unsigned long where_t;

  if (!enable_relax_relocs)
    return;

  /* Create and attach a BFD_RELOC_NDS32_LABEL fixup
     the size of instrcution may not be correct because
     it could be relaxable.  */
  exp.X_op = O_symbol;
  exp.X_add_symbol = section_symbol (now_seg);
  exp.X_add_number = 0;
  if (frag != frag_now)
    where_t = frag->fr_fix - byte_sz_p;
  else
    where_t = frag_now_fix () - byte_sz_p;

  fixP = fix_new_exp (frag, where_t, 0, &exp, 0, BFD_RELOC_NDS32_LABEL);
  /* Chain the fixup together.  */
  fixP->tc_fix_data = (fixS*) get_prev_fix ();
  fixP->fx_offset = label_align;
  label_exist = 0;
  label_align = 0;
  set_prev_fix (fixP);
}

static int
is_mfusr_pc (nds32_insn *insn)
{
  int insn_num;

  if (CGEN_INSN_BITSIZE (insn->insn) == 32)
    {
      insn_num = CGEN_INSN_NUM (insn->insn);
      if (insn_num != -1 && insn_num != NDS32_INSN_MFUSR)
	return 0;

      insn_num = INSN_VALUE (insn->buffer);
      return ((insn_num & INSN_MFUSR_PC_MASK) == INSN_MFUSR_PC);
    }
  else
    {
      return 0;
    }
}

static int last_fr_address = 0;

static int
check_instruction_availability (nds32_insn *insn, char *str)
{
  int insn_num = CGEN_INSN_NUM (insn->insn);

  if (is_mfusr_pc (insn) && march_cpu_opt == ARCH_V1)
    {
      /* V2 always support this instruction and has no this flag.  */
      nds32_flags |= E_NDS32_HAS_MFUSR_PC_INST;
    }
  else if ((CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_A32V2)
	    || CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_A16V2))
	   && march_cpu_opt == ARCH_V1)
    {
      /* V2 instruction used in V1 architecture.  */
      as_bad (_("instruction '%s' not supported in V1 architecture"), rem__r (str));
      return 0;
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_NOT_V3M)
	   && march_cpu_opt == ARCH_V3M)
    {
      as_bad (_("instruction '%s' not supported in V3M architecture"),
	      rem__r (str));
      return 0;
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_V3)
	   && (march_cpu_opt == ARCH_V1 || march_cpu_opt == ARCH_V2))
    {
      /* V3 instruction used in V1/V2 architecture
	 IFRET16 uses encoding of MOV55, so MOV55 is considered as a V3 instruction.
	 To correctly assemble mov55, an exception is created for mov55.  */
      if (insn_num != NDS32_INSN_MOV55)
	{
	  as_bad (_("V3 instruction '%s' not supported in (V1|V2) architecture"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_EXT))
    {
      /* Make sure that it is for C/C++ performance extension.  */
      if (enable_c_extension)
	{
	  nds32_flags |= E_NDS32_HAS_EXT_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling performance extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_EXT2))
    {
      /* Make sure that it is for C/C++ performance extension.  */
      if (enable_c_extension2)
	{
	  nds32_flags |= E_NDS32_HAS_EXT2_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling performance extension II"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_AUDIO))
    {
      /* Make sure that it is for C/C++ performance extension.  */
      if (enable_audio_extension)
	{
	  nds32_flags |= E_NDS32_HAS_AUDIO_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling AUDIO extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_STRING))
    {
      /* Make sure that it is for C/C++ performance extension.  */
      if (enable_string_extension)
	{
	  nds32_flags |= E_NDS32_HAS_STRING_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling STRING extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_DIV))
    {
      /* Make sure that it is for DIV extension.  */
      if (enable_div_extension)
	{
	  if (march_cpu_opt == ARCH_V1)
	    {
	      nds32_flags |= E_NDS32_HAS_DIV_INST;
	    }
	  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_DX_REG))
	    {
	      if (enable_dx_regs_extension)
		{
		  nds32_flags |= E_NDS32_HAS_DIV_DX_INST;
		}
	      else
		{
		  as_bad (_("instruction '%s' requires enabling DX_REGS extension"),
			  rem__r (str));
		  return 0;
		}
	    }
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling DIV extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_FPU_COM))
    {
      /* Make sure that it is for FPU extension.  */
      if (enable_fpu_sp_extension || enable_fpu_dp_extension)
	{
	  if (!(nds32_flags & (E_NDS32_HAS_FPU_INST | E_NDS32_HAS_FPU_DP_INST)))
	    {
	      /* Preserve information to decide which FPU bit will be enabled
		 in elf_nds32_final_processing.  */
	      nds32_fpu_com = 1;
	    }
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling FPU extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_FPU_SP))
    {
      /* Make sure that it is for FPU extension.  */
      if (enable_fpu_sp_extension)
	{
	  nds32_flags |= E_NDS32_HAS_FPU_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling FPU_SP extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_FPU_SP_MAC))
    {
      /* Make sure that it is for FPU extension.  */
      if (enable_fpu_sp_extension && enable_fpu_mac_extension)
	{
	  nds32_flags |= E_NDS32_HAS_FPU_MAC_INST;
	  nds32_flags |= E_NDS32_HAS_FPU_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling FPU_SP and FPU_MAC extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_FPU_DP))
    {
      /* Make sure that it is for FPU extension.  */
      if (enable_fpu_dp_extension)
	{
	  nds32_flags |= E_NDS32_HAS_FPU_DP_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling FPU_DP extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_FPU_DP_MAC))
    {
      /* Make sure that it is for FPU extension.  */
      if (enable_fpu_dp_extension && enable_fpu_mac_extension)
	{
	  nds32_flags |= E_NDS32_HAS_FPU_MAC_INST;
	  nds32_flags |= E_NDS32_HAS_FPU_DP_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling FPU_DP and FPU_MAC extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_FPU_BOTH))
    {
      /* Make sure that it is for FPU extension.  */
      if (enable_fpu_dp_extension && enable_fpu_sp_extension)
	{
	  nds32_flags |= E_NDS32_HAS_FPU_DP_INST;
	  nds32_flags |= E_NDS32_HAS_FPU_INST;
	}
      else
	{
	  as_bad (_("instruction '%s' requires enabling both FPU_DP and FPU_SP extension"),
		  rem__r (str));
	  return 0;
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_MAC))
    {
      /* Make sure that it is for MAC extension.  */
      if (enable_mac_extension)
	{
	  if (march_cpu_opt == ARCH_V1)
	    {
	      nds32_flags &= ~E_NDS32_HAS_NO_MAC_INST;
	    }
	  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_DX_REG))
	    {
	      if (enable_dx_regs_extension)
		{
		  nds32_flags |= E_NDS32_HAS_MAC_DX_INST;
		}
	      else
		{
		  as_bad (_("instruction '%s' requires enabling DX_REGS extension"),
			  rem__r (str));
		  return 0;
		}
	    }
	}
      else if (march_cpu_opt == ARCH_V1
	       || CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_DX_REG))
	{
	  as_bad (_("instruction '%s' requires enabling MAC extension"), rem__r (str));
	  return 0;
	}
    }
  else if (march_cpu_opt != ARCH_V1
	   && CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_DX_REG))
    {
      /* For DX_REG set but not for MAC, DIV, AUDIO.  */
      /* For example, mfusr, mtusr.  */

      insn_num = CGEN_INSN_NUM (insn->insn);
      if ((insn_num == NDS32_INSN_MFUSR
	   || insn_num == NDS32_INSN_MTUSR)
	  && CGEN_FIELDS_GROUPIDX (insn->fields) == 0
	  && CGEN_FIELDS_USRIDX (insn->fields) < 4
	  && CGEN_FIELDS_USRIDX (insn->fields) >= 0)
	{
	  if (enable_dx_regs_extension)
	    nds32_flags |= E_NDS32_HAS_MAC_DX_INST | E_NDS32_HAS_DIV_DX_INST;
	  else
	    {
	      as_bad (_("instruction '%s' requires enabling DX_REGS extension"),
		      rem__r (str));
	      return 0;
	    }
	}
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_IFCEXT))
    {
      nds32_flags |= E_NDS32_HAS_IFC_INST;
    }
  else if (CGEN_INSN_ATTR_VALUE (insn->insn, CGEN_INSN_STAT))
    {
      nds32_flags |= E_NDS32_HAS_SATURATION_INST;
    }
  return 1;
}

static int
get_instruction_attribute (nds32_insn *insn, int insn_num,
			   relax_substateT *subtype)
{
  int branch = 0, ind_branch = 0;

  switch (insn_num)
    {
    case NDS32_INSN_LMW_BI:
    case NDS32_INSN_LMW_BIM:
    case NDS32_INSN_LMW_BD:
    case NDS32_INSN_LMW_BDM:
    case NDS32_INSN_LMW_AI:
    case NDS32_INSN_LMW_AIM:
    case NDS32_INSN_LMW_AD:
    case NDS32_INSN_LMW_ADM:
    case NDS32_INSN_SMW_BI:
    case NDS32_INSN_SMW_BIM:
    case NDS32_INSN_SMW_BD:
    case NDS32_INSN_SMW_BDM:
    case NDS32_INSN_SMW_AI:
    case NDS32_INSN_SMW_AIM:
    case NDS32_INSN_SMW_AD:
    case NDS32_INSN_SMW_ADM:
      /* Make sure range register pair is in correct order.  */
      if (CGEN_FIELDS_RT5 (insn->fields) > CGEN_FIELDS_RB5 (insn->fields))
	{
	  as_bad (_("LMW/SMW register range out of order"));
	  return 0;
	}

      if (enable_reduce_regs)
	{
	  /* FIXME: This expression is so ugly.  */
	  if ((CGEN_FIELDS_RT5 (insn->fields) > REG_R10
	       || CGEN_FIELDS_RB5 (insn->fields) > REG_R10)
	      && ((CGEN_FIELDS_RT5 (insn->fields) != REG_R15
		  || CGEN_FIELDS_RB5 (insn->fields) != REG_R15)
		  && (CGEN_FIELDS_RT5 (insn->fields) != REG_SP
		      || CGEN_FIELDS_RB5 (insn->fields) != REG_SP)))
	    {
	      as_bad (_("LMW/SMW register range invalid"));
	      return 0;
	    }
	}

      break;

    case NDS32_INSN_J:
      branch = 1;
      subtype[0] |= RELAX_BRANCH_MASK | SET_BR_CODE (BR_UCOND_BR_S16M);
      break;

    case NDS32_INSN_JAL:
      branch = 1;
      subtype[0] |= RELAX_BRANCH_MASK | SET_BR_CODE (BR_UCOND_CALL_S16M);
      break;

    case NDS32_INSN_J8:
      branch = 1;
      subtype[0] |= RELAX_BRANCH_MASK | SET_BR_CODE (BR_UCOND_BR_S256);
      break;

    case NDS32_INSN_BEQZ:
    case NDS32_INSN_BNEZ:
    case NDS32_INSN_BGEZ:
    case NDS32_INSN_BLTZ:
    case NDS32_INSN_BGTZ:
    case NDS32_INSN_BLEZ:
      branch = 1;
      subtype[0] |= (CGEN_FIELDS_RT5 (insn->fields) << 27) | RELAX_BRANCH_MASK
		     | SET_BR_CODE (BR_COND_BR_S64K);
      break;

    case NDS32_INSN_BGEZAL:
    case NDS32_INSN_BLTZAL:
      branch = 1;
      subtype[0] |= (CGEN_FIELDS_RT5 (insn->fields) << 27) | RELAX_BRANCH_MASK
		    | SET_BR_CODE (BR_COND_CALL_S64K);
      break;

    case NDS32_INSN_BEQ:
    case NDS32_INSN_BNE:
      branch = 1;
      subtype[0] |= (CGEN_FIELDS_RT5 (insn->fields) << 27)
		    | (CGEN_FIELDS_RA5 (insn->fields) << 22) | RELAX_BRANCH_MASK
		    | SET_BR_CODE (BR_COND_BR_S16K);
      break;

    case NDS32_INSN_BEQC:
    case NDS32_INSN_BNEC:
      branch = 1;
      subtype[0] |= (CGEN_FIELDS_RT5 (insn->fields) << 27)
		    | RELAX_BRANCH_MASK | SET_BR_CODE (BR_COND_BR_S256);
      subtype[1] |= (CGEN_FIELDS_SIMM11 (insn->fields) << 21);
      break;

    case NDS32_INSN_JRAL:
    case NDS32_INSN_JRAL_ITON:
    case NDS32_INSN_JRAL_TON:
      ind_branch = 1;
      CGEN_FIELDS_RT5 (insn->fields) = (INSN_VALUE (insn->buffer) >> 20) & 0x1f;
      break;

    case NDS32_INSN_JRAL5:
    case NDS32_INSN_JR5:
    case NDS32_INSN_JR:
    case NDS32_INSN_JR_ITOFF:
    case NDS32_INSN_JR_TOFF:
    case NDS32_INSN_RET:
    case NDS32_INSN_RET_ITOFF:
    case NDS32_INSN_RET_TOFF:
    case NDS32_INSN_IRET:
    case NDS32_INSN_RET5:
    case NDS32_INSN_IFRET:
      ind_branch = 1;
      break;

    case NDS32_INSN_BEQZ38:
    case NDS32_INSN_BNEZ38:
      branch = 1;
      subtype[0] |= (CGEN_FIELDS_RT3 (insn->fields) << 27)
		    | RELAX_BRANCH_MASK | SET_BR_CODE (BR_COND_BR_S256);
      break;

    case NDS32_INSN_BEQS38:
    case NDS32_INSN_BNES38:
      branch = 1;
      subtype[0] |= (CGEN_FIELDS_RT3 (insn->fields) << 27)
		    | (REG_R5 << 22) | RELAX_BRANCH_MASK
		    | SET_BR_CODE (BR_COND_BR_S256);
      break;

    case NDS32_INSN_BEQZS8:
    case NDS32_INSN_BNEZS8:
      branch = 1;
      subtype[0] |= (REG_TA << 27) | RELAX_BRANCH_MASK
		    | SET_BR_CODE (BR_COND_BR_S256);
      break;
    case NDS32_INSN_IFCALL:
    case NDS32_INSN_IFCALL9:
      branch = 1;
      break;
    }

  /* Do not use 16 bit instruction in frag.  */
  if (disable_16bit)
    subtype[0] |= RELAX_FORCE_NO_16BIT_MASK;

  return (ind_branch << 1) | branch;
}

/* GAS will call this function for each input line which does not contain a
   pseudo-op.  The argument is a null terminated string.  The function should
   assemble the string as an instruction with operands.  Normally md_assemble
   will do this by calling frag_more and writing out some bytes (Frags).
   md_assemble will call fix_new to create fixups as needed (Fixups).  Targets
   which need to do special purpose relaxation will call frag_var.
   Depending on the optimization flag a convertible instruction my be converted
   from 16-bit to 32-bit or vice versa.

   -Os will try to convert all 32-bit instructions to 16-bit.
   -O  will try to align labels, visible or hidden, on boundary and convert as
       many 32-bit instructions as possible to 16-bit.  Occasionally, a
       convertible 16-bit instruction may be converted to 32-bit in order to
       align a label No conversion will happen if no optimization flag turned on.  */

/* This variable is used to record whether previous instruction
   is a branch or not.  If so, the current instruction should be
   expanded in 32-bit form in order to help branch prediction.

   `b2bb_prev' is set in md_assemble () depending on the current
   instruction.  And it is reset in nds32_elf_section_change_hook ().  */

void
md_assemble (char *str)
{
  nds32_insn insn;
  char *errmsg;
  relax_substateT subtype[NDS32_FRAG_FLAG_NUM];
  int branch;
  int ind_branch;
  int insn_num;
  int saved_endian;
  int relaxable = 0;
  fragS *fragP;
  const CGEN_OPINST *oi = NULL;
  nds32_insn_instant *insn_ins;
  struct nds32_pseudo_opcode *opcode;

  opcode = nds32_lookup_pseudo_opcode (str);
  /* Note that we need to check 'compiler_generated_asm' and 'opcode->physical_op'.
     If the assembly content is generated by compiler and this opcode is a physical instruction,
     there is no need to perform pseudo instruction expansion/transformation.  */
  if (opcode
      && !(compiler_generated_asm && opcode->physical_op))
    {
      nds32_pseudo_opcode_wrapper (str, opcode);
      return;
    }

  if (enable_reduce_regs && reg_out_of_range (str))
    {
      as_bad (_("instruction '%s' use invalid register not in "
		"Reduced Register Set"), rem__r (str));
    }

  /* COLE: I think the programmer should take care of this.
	   It's not assembler's resposibility.  Remove it someday.
	   Saddly, VLSI team need this now.  */
  nds32_adjust_label (1);

  /* Initialize GAS's cgen interface for a new instruction.  */
  gas_cgen_init_parse ();

  insn.insn = nds32_cgen_assemble_insn (gas_cgen_cpu_desc, str, &insn.fields,
					insn.buffer, &errmsg);
  if (!insn.insn)
    {
      as_bad (_("%s"), errmsg);
      return;
    }
  insn_num = CGEN_INSN_NUM (insn.insn);
  check_forbid_insn (CGEN_INSN_MNEMONIC (insn.insn), insn_num);
  if (!check_instruction_availability (&insn, str))
    return;

  subtype[0] = subtype[1] = 0;
  insn_num = convert_macro_insn_to_insn (&insn, &oi);

  branch = get_instruction_attribute (&insn, insn_num, subtype);
  ind_branch = (branch >> 1) & 1;
  branch = branch & 1;

  if (opt_b2bb && b2bb_prev && (branch || ind_branch))
    subtype[0] |= RELAX_FORCE_NO_16BIT_MASK;
  b2bb_prev = (branch || ind_branch);

  {
    finished_insnS fi;
    uint16_t insn16 = 0;
    int byte_sz = CGEN_INSN_BITSIZE (insn.insn) / 8;
    int org_byte_sz = byte_sz;
    int i;

    memset (fi.fixups, 0, sizeof (fixS *) * GAS_CGEN_MAX_FIXUPS);
    fi.num_fixups = 0;

    /* Doesn't really matter what we pass for RELAX_P here.
       This frag may have to be closed if it ends up with a branch instruction.
       Make sure the variable part and fixed part are in same fragment.  */
    frag_grow (byte_sz * 2);
    fragP = frag_now;

    /* COLE: Emit debug line before emit instruction;
	     otherwise, relax will mass it around.
		.loc 1 1 0
		.loc 1 2 0
		beqz	$r0, .L0

	In this case, when dwarf2_emit_line is called, by gas_cgen_finish_insn,
	for 'beqz', the symbol for line is tag to a new frag with negative offset
	pointed to the begining of 'beqz'.  If 'beqz' is relaxed to 'beqz38',
	the offset will point to two bytes ahead of 'beqz38' and cause negative
	advance pc.

	So why not just emit the line first? Hereby, the positive fixed offset
	can be used.  */

    dwarf2_emit_insn (0);
    if (byte_sz == 4)
      gas_cgen_finish_insn (insn.insn, insn.buffer,
			    CGEN_FIELDS_BITSIZE (&insn.fields), 1, &fi);
    else
      {
	insn.orig_insn = insn.insn;
	gas_cgen_finish_insn (insn.orig_insn, insn.buffer,
			      CGEN_FIELDS_BITSIZE (&insn.fields),
			      1 /* relax_p  */, &fi);
      }

    /* Comment for 16-bit: A 16-bit instruction may have to be expanded to
       32-bit and then contract to 16-bit again, so force to close this frag
       with 2 extra bytes to expand; remember this frag, so we can use it
       when we encounter a label later.

       If this is a branch, don't use it because it may never be contracted
       to 16-bit again once it expands.  */
    if (fragP != frag_now)
      {
	/* Comment for 16-bit:
	   This is a branch, it may expand to reach the target, so we can't
	   treat it as normal 16-bit instruction.  */
	if (branch)
	  {
	    /* Set tc_frag_data.fixup to NULL or address of LABEL relocation fixup.  */
	    while (fragP->fr_next != frag_now)
	      {
		/* Extra frag is created.  */
		fragP->tc_frag_data.fixup = NULL;
		fragP = fragP->fr_next;
		if ((prev_fixP = get_prev_fix ()))
		  prev_fixP->fx_where = 0;
	      }

	    if (optimize && label_exist)
	      append_label_reloc (fi.frag, byte_sz);

	    fragP->tc_frag_data.fixup = get_prev_fix ();
	    set_prev_fix (NULL);
	    RELAX_SET_FRAG_TC_FLAGS (fragP, subtype);
	    RELAX_SET_FRAG_TC_OPCNUM (fragP, insn_num);
	    for (i = 0; i < fi.num_fixups; i++)
	      if (fi.fixups[i] == NULL)
		{
		  relaxable = 1;
		  break;
		}
	  }
	else
	  {
	    /* Frag is closed due to no more space to expand.  */
	    fragP = frag_now;
	  }
      }
    else if (branch)
      {
	if (byte_sz == 4)
	  {
	    /* Not all branches has RELAXABLE attribute, this area is
	       used to process this kind of branches.
	       Ex. J, Jal;  */
	    if (fi.num_fixups)
	      {
		if ((fi.fixups[0]->fx_r_type - BFD_RELOC_UNUSED) == NDS32_OPERAND_CONCAT24)
		  fi.fixups[0]->fx_r_type = BFD_RELOC_NDS32_25_ABS;

		else if ((fi.fixups[0]->fx_r_type - BFD_RELOC_UNUSED) == NDS32_OPERAND_DISP24)
		  {
		    fi.fixups[0]->fx_r_type = BFD_RELOC_NDS32_25_PCREL;
		    fi.fixups[0]->fx_pcrel = 0;

		    if (!disable_16bit
			&& (optimize || optimize_for_space || optimize_for_space_no_align)
			&& (subtype[0] & RELAX_FORCE_NO_16BIT_MASK) == 0
			&& insn_num == NDS32_INSN_J
			&& fi.fixups[0]->fx_cgen.opinfo != BFD_RELOC_NDS32_25_ABS)
		      {
			expressionS exp_r;
			exp_r.X_op = O_symbol;
			exp_r.X_add_symbol = abs_section_sym;
			exp_r.X_add_number = 0;
			fix_new_exp (fi.fixups[0]->fx_frag,
				     fi.fixups[0]->fx_where, 4, &exp_r, 0,
				     BFD_RELOC_NDS32_INSN16);
		      }
		  }
		else if ((fi.fixups[0]->fx_r_type - BFD_RELOC_UNUSED) == NDS32_OPERAND_DISP16)
		  {
		    if (org_byte_sz == 4 && insn_num == NDS32_INSN_IFCALL)
		      {
			fi.fixups[0]->fx_r_type = BFD_RELOC_NDS32_17IFC_PCREL;
			fi.fixups[0]->fx_pcrel = 0;
			insn_ins = xmalloc (sizeof (nds32_insn_instant));
			assign_instant (insn_ins, insn_num, &fi, org_byte_sz, byte_sz, &insn,
					relaxable, oi);
			insert_relax_type (insn_ins, BFD_RELOC_NDS32_INSN16,
					     4, 0, NULL);
		      }
		    else
		      {
			fi.fixups[0]->fx_r_type = BFD_RELOC_NDS32_17_PCREL;
			fi.fixups[0]->fx_pcrel = 0;
		      }
		  }
		else if ((fi.fixups[0]->fx_r_type - BFD_RELOC_UNUSED) == NDS32_OPERAND_DISP14)
		  {
		    fi.fixups[0]->fx_r_type = BFD_RELOC_NDS32_15_PCREL;
		    fi.fixups[0]->fx_pcrel = 0;
		  }
		else if ((fi.fixups[0]->fx_r_type - BFD_RELOC_UNUSED) == NDS32_OPERAND_DISP8)
		  {
		    fi.fixups[0]->fx_r_type = BFD_RELOC_NDS32_WORD_9_PCREL;
		    fi.fixups[0]->fx_pcrel = 0;
		  }
	      }
	    else
	      as_warn (_("Branch instruction '%s' with absolute offset is dangerous."),
		       rem__r (str));
	  }
	else /* byte_sz == 2  */
	  {

	    /* Not all branches has RELAXABLE attribute, this area is
	       used to process this kind of branches.
	       Ex. J, Jal;  */

	    /* Turn off fx_pcrel to prevent r_addend set as pc-relative offset
	       but set as a section-relative offset
	       Set fx_no_overflow to bypass the check of large symbol value of
	       short instruction.  (e.g., 0x10000 for 16-bit instruction.)  */
	    if (fi.num_fixups)
	      {
		if ((fi.fixups[0]->fx_r_type - BFD_RELOC_UNUSED) == NDS32_OPERAND_HSDISP8)
		  {
		    fi.fixups[0]->fx_r_type = BFD_RELOC_NDS32_9_PCREL;
		    fi.fixups[0]->fx_pcrel = 0;
		    fi.fixups[0]->fx_no_overflow = 1;
		  }
		else if ((fi.fixups[0]->fx_r_type - BFD_RELOC_UNUSED) == NDS32_OPERAND_DISP9)
		  {
		    fi.fixups[0]->fx_r_type = BFD_RELOC_NDS32_10_UPCREL;
		    fi.fixups[0]->fx_pcrel = 0;
		    fi.fixups[0]->fx_no_overflow = 1;
		  }
	      }
	    else
	      as_warn (_("Branch instruction '%s' with absolute offset is dangerous."),
		       rem__r (str));

	    /* br && no RELAXABLE attribute.
	       Complete frag for this instruction may expand to 4-byte
	       maybe this aprt can be commented out?  */
	    frag_var (rs_machine_dependent, 0, 0,
		      0 /*subtype  */, NULL, 0, NULL);
	    if (optimize && label_exist)
	      append_label_reloc (fi.frag, 2);
	    fragP->tc_frag_data.fixup = get_prev_fix ();
	    set_prev_fix (NULL);
	  }
      }
    else
      {
	if (byte_sz == 2)
	  {
	    if (insn_num == NDS32_INSN_LWI45_FE)
	      {
		for (i = 0; i < fi.num_fixups; i++)
		  {
		    if (fi.fixups[i] == NULL)
		      break;
		    else if (fi.fixups[i]->fx_cgen.opinfo == BFD_RELOC_NDS32_MINUEND)
		      {
			break;
		      }
		  }
	      }
	  }
      }

    /* The fragP->last_fr_address will be used when estimating the size of
       fragments.  It is just used to stored the index of the fragment here.  */
    if (fragP->last_fr_address == 0)
      {
	fragP->last_fr_address = last_fr_address;
	last_fr_address++;
      }

    if (byte_sz == 4)
      {
	if (!fi.num_fixups && !disable_16bit
	    && (optimize || optimize_for_space || optimize_for_space_no_align)
	    && convert_32_to_16 (fragP, &insn16, &subtype[0], &insn_num))
	  {
	    uint32_t old_insn =
	      bfd_getb32 (fragP->fr_literal + frag_now_fix_octets () - 4);

	    /* We have no way to know whether a 32-bit insn is convertible
	       or not if it has fixup (ie symbol)
	       optimize is on, so make a frag to contracts convertible insn.  */

	    frag_var (rs_machine_dependent, 0, 0, 0 /* subtype[0]  */,
		      NULL, 0, NULL);
	    RELAX_SET_FRAG_TC_FLAGS (fragP, subtype);
	    RELAX_SET_FRAG_TC_OPCNUM (fragP, insn_num);

	    /* Modify to 16-bit, instruction is always big endian.  */
	    saved_endian = target_big_endian;
	    target_big_endian = 1;
	    md_number_to_chars (fragP->fr_literal + fragP->fr_fix - 4, insn16, 2);
	    target_big_endian = saved_endian;
	    fragP->fr_fix -= 2;

	    /* Always mark it as a 16-bit instruction.  */
	    /* No INSN16 relocation is needed.  */
	    if (optimize && !branch)
	      {
		/* For 32-to-16 bit branches,
		   the label relocs have already stored.  */
		if (optimize && label_exist)
		  append_label_reloc (fi.frag, 2);

		fragP->tc_frag_data.fixup = get_prev_fix ();
		set_prev_fix (NULL);

		/* Mark as relaxable in order to align label.  */
		RELAX_SET_RELAXABLE (fragP);
		RELAX_SET_INSN (fragP, old_insn);
	      }
	  }
      }
    else /* byte_sz == 2  */
      {
	if (!branch && optimize)
	  {
	    uint32_t insn32;
	    uint16_t tmp16;

	    tmp16 = bfd_getb16 (frag_now->fr_literal + frag_now_fix () - 2);
	    if (nds32_convert_16_to_32 (stdoutput, tmp16, &insn32))
	      {
		/* Not a br.  This frag needs to be expanded.  */
		frag_grow (2);
		frag_var (rs_machine_dependent, 2, 0,
			  0 /* subtype[0]  */, NULL, 0, NULL);
		RELAX_SET_FRAG_TC_FLAGS (fragP, subtype);
		RELAX_SET_FRAG_TC_OPCNUM (fragP, insn_num);

		/* Mark as relaxable in order to align label.  */
		RELAX_SET_RELAXABLE (fragP);
	      }

	    if (optimize && label_exist)
	      append_label_reloc (fi.frag, 2);

	    fragP->tc_frag_data.fixup = get_prev_fix ();
	    set_prev_fix (NULL);
	  }
      }

    /* Create an instruction node and insert it into a proper basic block.  */
    insn_ins = xmalloc (sizeof (nds32_insn_instant));
    if (insn16 != 0)
      byte_sz = 2;
    assign_instant (insn_ins, insn_num, &fi, org_byte_sz, byte_sz, &insn,
		    relaxable, oi);
    if (bb_now->insn_head == NULL)
      bb_now->insn_head = insn_ins;
    bb_now->insn_tail = insn_ins;

    /* Build a list to connect all sethi instructions.  */
    if (org_byte_sz == 4 && insn_num == NDS32_INSN_SETHI)
      {
	for (i = 0; i < insn_ins->num_fixups; i++)
	  {
	    if (insn_ins->fixups[i]->fx_cgen.opinfo == BFD_RELOC_NDS32_HI20
		|| insn_ins->fixups[i]->fx_cgen.opinfo == BFD_RELOC_NDS32_GOT_HI20
		|| insn_ins->fixups[i]->fx_cgen.opinfo == BFD_RELOC_NDS32_GOTOFF_HI20
		|| insn_ins->fixups[i]->fx_cgen.opinfo == BFD_RELOC_NDS32_PLTREL_HI20
		|| insn_ins->fixups[i]->fx_cgen.opinfo == BFD_RELOC_NDS32_PLT_GOTREL_HI20)
	      {
		push_insn_to_list (&nds32_hi_insn_list, insn_ins);
		break;
	      }
	  }
      }

    /* Create a new basic block if current instruction is a branch.  */
    if (branch || ind_branch)
      create_new_basic_block ();

    if (optimize && label_exist)
      append_label_reloc (fi.frag, byte_sz);

  }

  /* If current instruction is JAL, JRAL, BGEZAL, BLTZAL or JRAL5
     the next instruction must be treated as having a label when optimize for
     speed.  A label relocation must be added and alignment must be enforced.  */
  if (optimize)
    {
      switch (insn_num)
	{
	case NDS32_INSN_JAL:
	case NDS32_INSN_JRAL:
	case NDS32_INSN_BGEZAL:
	case NDS32_INSN_BLTZAL:
	case NDS32_INSN_JRAL5:
	  label_exist = 1;
	  break;
	}
    }
}

/* md_macro_start  */

void
nds32_macro_start (void)
{
  /* Maximum number of levels.  */
  if (macro_level >= MAX_MACRO_LEVEL - 1)
    as_fatal (_("macros nested too deeply, only allows 32 nesting."));

  ++macro_level;
  builtin_hash[macro_level] = hash_new ();
  local_label_hash[macro_level] = hash_new ();
}

/* md_macro_info  */

void
nds32_macro_info (void *info)
{
  formal_entry *entry;
  macro_entry *macro = (macro_entry *) info;

  /* Put the formal arguments into the substitution symbol table.  */
  for (entry = macro->formals; entry; entry = entry->next)
    {
      char *name = strncpy (xmalloc (entry->name.len + 1),
			    entry->name.ptr, entry->name.len);
      char *value = strncpy (xmalloc (entry->actual.len + 1),
			     entry->actual.ptr, entry->actual.len);

      name[entry->name.len] = '\0';
      value[entry->actual.len] = '\0';
      hash_insert (builtin_hash[macro_level], name, value);
    }
}

/* md_macro_end  */

void
nds32_macro_end (void)
{
  hash_die (builtin_hash[macro_level]);
  builtin_hash[macro_level] = NULL;
  hash_die (local_label_hash[macro_level]);
  local_label_hash[macro_level] = NULL;
  --macro_level;
}

/* GAS will call this function with one argument, an expressionS pointer, for
   any expression that can not be recognized.  When the function is called,
   input_line_pointer will point to the start of the expression.  */

void
md_operand (expressionS *expressionP)
{
  if (*input_line_pointer == '#')
    {
      input_line_pointer++;
      expression (expressionP);
    }
}

/* GAS will call this function for each section at the end of the assembly, to
   permit the CPU back end to adjust the alignment of a section.  The function
   must take two arguments, a segT for the section and a valueT for the size of
   the section, and return a valueT for the rounded size.  */

valueT
md_section_align (segT segment, valueT size)
{
  int align = bfd_get_section_alignment (stdoutput, segment);

  return ((size + (1 << align) - 1) & (-1 << align));
}

/* GAS will call this function when a symbol table lookup fails, before it
   creates a new symbol.  Typically this would be used to supply symbols whose
   name or value changes dynamically, possibly in a context sensitive way.
   Predefined symbols with fixed values, such as register names or condition
   codes, are typically entered directly into the symbol table when md_begin
   is called.  One argument is passed, a char * for the symbol.  */

symbolS *
md_undefined_symbol (char *name ATTRIBUTE_UNUSED)
{
  return NULL;
}

/* Can a branch instruction be converted to 16-bit?  */

static int
is_convertible (fragS *fragP)
{
  switch (RELAX_OPC_NUM (fragP))
    {
    case NDS32_INSN_JRAL:
    case NDS32_INSN_JRAL5:
    case NDS32_INSN_J8:
    case NDS32_INSN_JR:
    case NDS32_INSN_JR5:
    case NDS32_INSN_RET:
    case NDS32_INSN_RET5:
    case NDS32_INSN_BEQS38:
    case NDS32_INSN_BNES38:
    case NDS32_INSN_BEQZ38:
    case NDS32_INSN_BNEZ38:
    case NDS32_INSN_BEQZS8:
    case NDS32_INSN_BNEZS8:
      return 1;
      break;

    case NDS32_INSN_BEQ:
    case NDS32_INSN_BNE:
      if ((RELAX_RT (fragP) < REG_R8 && RELAX_RA (fragP) == REG_R5
	   && RELAX_RT (fragP) != REG_R5)
	  || (RELAX_RA (fragP) < REG_R8
	      && RELAX_RT (fragP) == REG_R5
	      && RELAX_RA (fragP) != REG_R5))
	{
	  return 1;
	}
      else
	{
	  return 0;
	}
      break;

    case NDS32_INSN_BEQZ:
    case NDS32_INSN_BNEZ:
      if (RELAX_RT (fragP) < REG_R8 || RELAX_RT (fragP) == REG_R15)
	{
	  return 1;
	}
      else
	{
	  return 0;
	}
      break;

    default:
      return 0;
    }
}

/* Adjust frag address due to backward relax; after this adjustment all frags
   from the relaxed frag to current or the last frag are at correct address.  */

static void
adj_frag_addr (fragS *startP, fragS *endP, int adj)
{
  while (startP)
    {
      startP = startP->fr_next;
      if (startP)
	{
	  startP->fr_address += adj;
	  if (startP == endP)
	    {
	      break;
	    }
	}
    }
}

static void
add_label_reloc (fragS *fragP)
{
  fixS *fixP;

  if (!enable_relax_relocs)
    return;

  if (fragP->fr_next)
    {
      expressionS exp;

      /* More frags follow this frag.  */
      if (!fragP->fr_next->tc_frag_data.fixup)
	{
	  /* Next frag has no LABEL reloc; add LABEL reloc to next frag.  */
	  /* No existing LABEL reloc, OK to add one.  */
	  exp.X_op = O_symbol;
	  exp.X_add_symbol = abs_section_sym;
	  exp.X_add_number = 0;
	  fixP = fix_new_exp (fragP->fr_next, 0,
			      0, &exp, 0, BFD_RELOC_NDS32_LABEL);
	  fragP->fr_next->tc_frag_data.fixup = fixP;
	}
      else
	{
	  /* LABEL reloc existed; check to see if it is at the beginning
	     of next frag; if so just do nothing, else chain it together.  */
	  fixP = (fixS *) fragP->fr_next->tc_frag_data.fixup;
	  while (fixP)
	    {
	      if (fixP->fx_where == 0)
		{
		  /* LABEL reloc at the beginning.  */
		  return;
		}
	      /* If it not null, it means there is label fix.  */
	      fixP = (fixS *) fixP->tc_fix_data;
	    }

	  /* No LABEL reloc at the beginning.  */
	  exp.X_op = O_symbol;
	  exp.X_add_symbol = abs_section_sym;
	  exp.X_add_number = 0;
	  fixP = fix_new_exp (fragP->fr_next, 0,
			      0, &exp, 0, BFD_RELOC_NDS32_LABEL);

	  fixP->tc_fix_data = (fixS*) fragP->fr_next->tc_frag_data.fixup;
	  fragP->fr_next->tc_frag_data.fixup = fixP;
	}

    }
}


/* Estimate the size of branch instruction sequence.

   fragP: ptr to the target frag
   segment: segment the frag is in
   first_time: set to 1 if estimation for the first time else set to 0
   return value: size difference after estimation.  */

static int
calc_branch_seq_size (fragS *fragP,
		      segT segment, int first_time, long stretch)
{
  long offset;
  long size;
  long insn_size;
  int org_size;
  int off;
  BR_RANGE_TYPE insn_range = 0;
  BR_RANGE_TYPE third_higher = 0;
  BR_RANGE_TYPE min_range = 0;
  BR_RANGE_TYPE sym_range = 0;
  BR_SEQ_TYPE code_seq;
  int adj = 0;

  adj = adj_label_pair (fragP);

  /* A branch without symbol is not relaxable, do nothing.  */
  if (fragP->fr_symbol == NULL)
    {
      if (RELAX_RELAXABLE (fragP))
	{
	  prev_frag = fragP;
	}
      return adj;
    }

  off = 0;
  switch (RELAX_OPC_NUM (fragP))
    {
    case NDS32_INSN_J:
      insn_range = BR_RANGE_S16M;
      insn_size = 4;
      org_size = 4;
      off = 4;
      code_seq = BR_UCOND_BR_S16M;
      break;

    case NDS32_INSN_JAL:
      insn_range = BR_RANGE_S16M;
      insn_size = 4;
      org_size = 4;
      off = 4;
      code_seq = BR_UCOND_CALL_S16M;
      break;

    case NDS32_INSN_BGEZAL:
    case NDS32_INSN_BLTZAL:
      insn_range = BR_RANGE_S64K;
      insn_size = 4;
      org_size = 4;
      off = 4;
      code_seq = BR_COND_CALL_S64K;
      break;

    case NDS32_INSN_BEQZ:
    case NDS32_INSN_BNEZ:
    case NDS32_INSN_BGEZ:
    case NDS32_INSN_BLTZ:
    case NDS32_INSN_BGTZ:
    case NDS32_INSN_BLEZ:
      third_higher = BR_RANGE_S64K;
      insn_range = BR_RANGE_S64K;
      insn_size = 4;
      org_size = 4;
      off = 4;
      code_seq = BR_COND_BR_S64K;
      break;

    case NDS32_INSN_BEQ:
    case NDS32_INSN_BNE:
      third_higher = BR_RANGE_S16K;
      insn_range = BR_RANGE_S16K;
      insn_size = 4;
      org_size = 4;
      off = 4;
      code_seq = BR_COND_BR_S16K;
      break;

    case NDS32_INSN_BEQC:
    case NDS32_INSN_BNEC:
      third_higher = BR_RANGE_S256;
      insn_range = BR_RANGE_S256;
      insn_size = 4;
      org_size = 4;
      off = 4;
      code_seq = BR_COND_BR_S256;
      break;

    case NDS32_INSN_JR:
    case NDS32_INSN_RET:
      insn_range = BR_RANGE_U4G;
      insn_size = 4;
      org_size = 4;
      off = 4;
      code_seq = BR_UCOND_BR_U4G;
      break;

    case NDS32_INSN_JRAL:
      insn_range = BR_RANGE_U4G;
      insn_size = 4;
      org_size = 4;
      off = 4;
      code_seq = BR_UCOND_CALL_U4G;
      break;

    case NDS32_INSN_J8:
      insn_range = BR_RANGE_S256;
      insn_size = 2;
      org_size = 2;
      off = 2;
      code_seq = BR_UCOND_BR_S256;
      break;

    case NDS32_INSN_BEQS38:
    case NDS32_INSN_BNES38:
      third_higher = BR_RANGE_S16K;
      insn_range = BR_RANGE_S256;
      insn_size = 2;
      org_size = 2;
      off = 2;
      code_seq = BR_COND_BR_S256;
      break;

    case NDS32_INSN_BEQZ38:
    case NDS32_INSN_BNEZ38:
    case NDS32_INSN_BEQZS8:
    case NDS32_INSN_BNEZS8:
      third_higher = BR_RANGE_S64K;
      insn_range = BR_RANGE_S256;
      insn_size = 2;
      org_size = 2;
      off = 2;
      code_seq = BR_COND_BR_S256;
      break;

    case NDS32_INSN_JR5:
    case NDS32_INSN_RET5:
      insn_range = BR_RANGE_U4G;
      insn_size = 2;
      org_size = 2;
      off = 2;
      code_seq = BR_UCOND_BR_U4G;
      break;

    case NDS32_INSN_JRAL5:
      insn_range = BR_RANGE_U4G;
      insn_size = 2;
      org_size = 2;
      off = 2;
      code_seq = BR_UCOND_CALL_U4G;
      break;

    default:
      insn_size = 0;
      org_size = 0;
      off = 0;
      code_seq = BR_SEQ_NONE;
      break;
    }

  if (!optimize && !optimize_for_space && !optimize_for_space_no_align)
    {
      /* Remember range of original instruction.  */
      min_range = insn_range;
    }

  if (!first_time)
    {
      code_seq = RELAX_SEQ_TYPE (fragP);
      /* Get previous code sequence.  */
      switch (code_seq)
	{
	case BR_UCOND_BR_S256:
	  /* PC relative -256 to 254 unconditional branch.  */
	  insn_range = BR_RANGE_S256;
	  insn_size = RELAX_RELAXED (fragP) ? 4 : 2;
	  off = insn_size;
	  break;

	case BR_COND_BR_S256:
	  /* PC relative -256 to 254 conditional branch.  */
	  insn_range = BR_RANGE_S256;
	  insn_size = RELAX_RELAXED (fragP) ? 4 : 2;
	  if (RELAX_OPC_NUM (fragP) == NDS32_INSN_BEQS38
	      || RELAX_OPC_NUM (fragP) == NDS32_INSN_BNES38)
	    {
	      third_higher = BR_RANGE_S16K;
	    }
	  else if (RELAX_OPC_NUM (fragP) == NDS32_INSN_BEQC
		   || RELAX_OPC_NUM (fragP) == NDS32_INSN_BNEC)
	    {
	      insn_size = 4;
	    }
	  else
	    {
	      third_higher = BR_RANGE_S64K;
	    }
	  off = insn_size;
	  break;

	case BR_COND_BR_S16K:
	  /* PC relative -16K to 16K - 2 conditional branch.  */
	  insn_range = BR_RANGE_S16K;
	  if (RELAX_OPC_NUM (fragP) == NDS32_INSN_BEQC
	      || RELAX_OPC_NUM (fragP) == NDS32_INSN_BNEC)
	    insn_size = 6;
	  else
	    {
	      third_higher = BR_RANGE_S16K;
	      insn_size = 4;
	    }
	  off = 4;
	  break;

	case BR_COND_CALL_S64K:
	  /* PC relative -64K to 64K -2 conditional call.  */
	  insn_range = BR_RANGE_S64K;
	  insn_size = 4;
	  off = insn_size;
	  break;

	case BR_COND_BR_S64K:
	  /* PC relative -64K to 64K - 2 conditional branch.  */
	  insn_range = BR_RANGE_S64K;
	  third_higher = BR_RANGE_S64K;
	  insn_size = 4;
	  off = insn_size;
	  break;

	case BR_UCOND_CALL_S16M:
	  /* PC relative -16M to 16M -2 unconditional call.  */
	  insn_range = BR_RANGE_S16M;
	  insn_size = 4;
	  off = insn_size;
	  break;

	case BR_COND_CALL_S16M:
	  /* PC relative -16M to 16M -2 conditional call.  */
	  insn_range = BR_RANGE_S16M;
	  insn_size = 8;
	  off = 4;
	  break;

	case BR_UCOND_BR_S16M:
	  /* PC relative -16M to 16M -2 unconditional branch.  */
	  insn_range = BR_RANGE_S16M;
	  insn_size = 4;
	  off = insn_size;
	  break;

	case BR_COND_BR_S16M:
	  /* PC relative -16M to 16M - 2 conditional branch.  */
	  insn_range = BR_RANGE_S16M;
	  insn_size = (RELAX_USE_32BIT (fragP) || optimize
		       || !is_convertible (fragP))
		      ? 8 : 6;
	  off = 4;
	  break;

	case BR_UCOND_CALL_U4G:
	  /* Absolute 0 to 4G - 2 unconditional call.  */
	  insn_range = BR_RANGE_U4G;
	  if (RELAX_USE_32BIT (fragP) || optimize)
	    {
	      insn_size = 12;
	      off = 4;
	    }
	  else
	    {
	      insn_size = 10;
	      off = 2;
	    }
	  break;

	case BR_COND_CALL_U4G:
	  /* Absolute 0 to 4G - 2 conditional call.  */
	  insn_range = BR_RANGE_U4G;
	  insn_size = (RELAX_USE_32BIT (fragP) || optimize) ? 16 : 14;
	  off = (RELAX_USE_32BIT (fragP) || optimize) ? 4 : 2;
	  break;

	case BR_UCOND_BR_U4G:
	  /* Absolute 0 to 4G - 2 unconditional branch.  */
	  insn_range = BR_RANGE_U4G;
	  insn_size = (RELAX_USE_32BIT (fragP) || optimize) ? 12 : 10;
	  off = (RELAX_USE_32BIT (fragP) || optimize) ? 4 : 2;
	  break;

	case BR_COND_BR_U4G:
	  /* Absolute 0 to 4G - 2 conditional branch.  */
	  insn_range = BR_RANGE_U4G;
	  if (RELAX_USE_32BIT (fragP)
	      || (!is_convertible (fragP) && optimize))
	    {
	      insn_size = 16;
	      off = 4;
	    }
	  else if (is_convertible (fragP))
	    {
	      insn_size = 12;
	      off = 2;
	    }
	  else
	    {
	      insn_size = 14;
	      off = 2;
	    }
	  break;

	default:
	  return 0;
	  break;
	}
    }

  if (S_GET_SEGMENT (fragP->fr_symbol) != segment
      || S_IS_WEAK (fragP->fr_symbol))
    {
      /* The symbol is undefined in this segment.
	 Change the relaxation subtype to the max allowable and leave
	 all further handling to md_convert_frag.  */

      /* This symbol could be far far away, use longest instruction sequence,
	 and let linker relaxes it.  */

      offset = 0x80000000;
    }
  else
    {
      /* This is local symbol.  */
      addressT addr;
      offsetT val;

      /* Calculate symbol address and instruction address.  */
      if (S_GET_VALUE (fragP->fr_symbol) > fragP->fr_address)
	{
	  val = (S_GET_VALUE (fragP->fr_symbol) + stretch) + fragP->fr_offset;
	  addr = fragP->fr_address + fragP->fr_fix - org_size;
	}
      else
	{
	  val = S_GET_VALUE (fragP->fr_symbol) + fragP->fr_offset;
	  addr = fragP->fr_address + fragP->fr_fix - org_size + insn_size - off;
	}

      /* Calculate pc relative offset.  */
      offset = val - addr;
    }

  if (offset >= -(0x100) && offset < 0x100)
    {
      /* +- 256 bytes, 16-bit instruction is possible.  */
      sym_range = BR_RANGE_S256;
    }
  else if (offset >= -(0x4000) && offset < 0x4000)
    {
      /* +- 16K, 32-bit conditional branch.  */
      sym_range = BR_RANGE_S16K;
    }
  else if (offset >= -(0x10000) && offset < 0x10000)
    {
      /* +- 64K, 32-bit conditional branch.  */
      sym_range = BR_RANGE_S64K;
    }
  else if (offset >= -(0x1000000) && offset < 0x1000000)
    {
      /* +- 16M, 32-bit unconditional branch.  */
      sym_range = BR_RANGE_S16M;
    }
  else
    {
      /* cases above this one are all pc relative
	 4G, direct or indirect branch.  */
      sym_range = BR_RANGE_U4G;
    }

  if (!optimize && !optimize_for_space && !optimize_for_space_no_align)
    {
      if (sym_range < min_range)
	sym_range = min_range;
    }

  /* 16-bit branch is a special case; we want to expand it if it is in range and
     optimize for speed is on.  */
  if (sym_range == insn_range)
    {
      /* Range no change.  */
      if ((code_seq == BR_COND_BR_S256 || code_seq == BR_UCOND_BR_S256)
	  && is_convertible (fragP))
	{
	  if (optimize)
	    {
	      /* Mark as relaxable.  */
	      RELAX_SET_RELAXABLE (fragP);
	    }
	  else if (optimize_for_space || optimize_for_space_no_align)
	    {
	      /* Mark as relaxed.  */
	      RELAX_SET_RELAXABLE (fragP);
	      RELAX_CLEAR_RELAXED (fragP);
	    }
	}

      if (RELAX_RELAXABLE (fragP))
	{
	  prev_frag = fragP;
	}

      RELAX_SET_FRAG_TC_FLAG (0, fragP, ((RELAX_GET_FRAG_TC_FLAG (0, fragP)
					  & (~RELAX_SEQ_TYPE_MASK))
					 | code_seq << 10));

      return (first_time && RELAX_RELAXED (fragP)) ? 2 + adj : adj;
    }

  /* Reset flags.  */
  RELAX_CLEAR_RELAXABLE (fragP);
  RELAX_CLEAR_RELAXED (fragP);

  switch (code_seq)
    {
    case BR_UCOND_CALL_S16M:
    case BR_UCOND_CALL_U4G:
      if (sym_range > BR_RANGE_S16M)
	{
	  /* sethi   $ta, hi20(lable)
	     ori     $ta, $ta, lo12(label)
	     jral(5) $ta
	     Size is 10 or 12 bytes.  */
	  code_seq = BR_UCOND_CALL_U4G;

	  if (pic_code && (S_GET_SEGMENT (fragP->fr_symbol) != segment
			   || S_IS_WEAK (fragP->fr_symbol)))
	    size = 16;
	  else
	    size = (RELAX_USE_32BIT (fragP) || optimize) ? 12 : 10;
	}
      else
	{
	  /* jal  label  */
	  code_seq = BR_UCOND_CALL_S16M;
	  size = 4;
	}
      break;

    case BR_COND_CALL_S64K:
    case BR_COND_CALL_S16M:
    case BR_COND_CALL_U4G:
      if (sym_range > BR_RANGE_S16M)
	{
	  /* bltz    rt, $1
	     sethi   $ta, hi20(label)
	     ori     $ta, $ta, lo12(label)
	     jral(5) $ta
	     $1:
	     Size is 14 or 16 bytes.  */
	  code_seq = BR_COND_CALL_U4G;
	  if (pic_code && (S_GET_SEGMENT (fragP->fr_symbol) != segment
			   || S_IS_WEAK (fragP->fr_symbol)))
	    size = 16;
	  else
	    size = (RELAX_USE_32BIT (fragP) || optimize) ? 16 : 14;
	}
      else if (sym_range > BR_RANGE_S64K)
	{
	  /* bltz rt, $1
	     jal  label
	     $1:
	     Size is 8 bytes.  */
	  code_seq = BR_COND_CALL_S16M;
	  size = 8;
	}
      else
	{
	  /* bgezal label
	     Size is 4 bytes.  */
	  code_seq = BR_COND_CALL_S64K;
	  size = 4;
	}

      break;

    case BR_UCOND_BR_S256:
    case BR_UCOND_BR_S16M:
    case BR_UCOND_BR_U4G:
      if (sym_range > BR_RANGE_S16M)
	{
	  /* sethi   $ta, hi20(label)
	     ori     $ta, $ta, lo12(label)
	     jral(5) $ta
	     Size is 10 or 12 bytes.  */
	  code_seq = BR_UCOND_BR_U4G;
	  size = (RELAX_USE_32BIT (fragP) || optimize) ? 12 : 10;
	}
      else if (sym_range > BR_RANGE_S256 || (RELAX_USE_32BIT (fragP)))
	{
	  /* j label
	     Size is 4 bytes.  */
	  code_seq = BR_UCOND_BR_S16M;
	  size = 4;
	}
      else
	{
	  /* 16-bit branch.  */
	  /* Mark this instruction.  */
	  code_seq = BR_UCOND_BR_S256;
	  size = 2;
	  if (optimize)
	    {
	      /* Mark as relaxable.  */
	      RELAX_SET_RELAXABLE (fragP);
	    }
	  else if (optimize_for_space || optimize_for_space_no_align)
	    {
	      /* Mark as relaxed.  */
	      RELAX_SET_RELAXABLE (fragP);
	      RELAX_CLEAR_RELAXED (fragP);
	    }
	}

      break;

    case BR_COND_BR_S256:
    case BR_COND_BR_S16K:
    case BR_COND_BR_S64K:
    case BR_COND_BR_S16M:
    case BR_COND_BR_U4G:
      if (sym_range > BR_RANGE_S16M)
	{
	  add_label_reloc (fragP);
	  code_seq = BR_COND_BR_U4G;
	  if (RELAX_USE_32BIT (fragP)
	      || (optimize && !is_convertible (fragP)))
	    {
	      /* bne   rt, $lp, $1 or bnez rt, $1
		 sethi $ta, hi20(label)
		 ori   $ta, $ta, lo12(label)
		 jr    $ta
		 $1:  */
	      size = 16;
	    }
	  else
	    {
	      if (is_convertible (fragP))
		{
		  /* Original instruction can covert to 16-bit.
		     bnes38 rt3, $1 or bnez38 rt3, $1
		     sethi  $ta, hi20(label)
		     ori    $ta, $ta, lo12(label)
		     jr5    $ta
		     $1:  */
		  size = 12;
		}
	      else
		{
		  /* bne   rt, $lp, $1 or bnez rt, $1
		     sethi $ta, hi20(label)
		     ori   $ta, $ta, lo12(label)
		     jr5   $ta
		     $1:  */
		  size = 14;
		}
	    }
	}
      else if (sym_range > third_higher)
	{
	  add_label_reloc (fragP);
	  /* beqc rt, imm11s, imm8s  */
	  if (RELAX_OPC_NUM (fragP) == NDS32_INSN_BEQC
	      || RELAX_OPC_NUM (fragP) == NDS32_INSN_BNEC)
	    {
	      if (!RELAX_USE_32BIT (fragP) && sym_range <= BR_RANGE_S16K
		  && RELAX_SIMM11 (fragP) < 16 && RELAX_SIMM11 (fragP) >= -16)
		{
		  /* movi55 $ta, imm11s (-16 <= imm11s < 16)
		     beq    rt, $ta, imm8s  */
		  code_seq = BR_COND_BR_S16K;
		  size = 6;
		}
	      else
		{
		  /* movi $ta, imm11s
		     beq  rt, $ta, imm8s  */
		  code_seq = BR_COND_BR_S16M;
		  size = 8;
		}
	    }
	  /* range > +/-16K or +/-64K  */
	  /* Create LABEL reloc for next frag and attach to it.  */
	  else if (RELAX_USE_32BIT (fragP) || optimize
		   || !is_convertible (fragP))
	    {
	      /* bnez rt, $1 ; this insn could be 16-bit
		 j    label
		 $1:
		 Size is 8 bytes.  */
	      code_seq = BR_COND_BR_S16M;
	      size = 8;
	    }
	  else
	    {
	      /* bnez38 rt3, $1
		 j      label
		 $1:
		 Size is 6 bytes.  */
	      code_seq = BR_COND_BR_S16M;
	      size = 6;
	    }
	}
      else if (sym_range <= BR_RANGE_S256 && is_convertible (fragP)
	       && !(RELAX_USE_32BIT (fragP)))
	{
	  /* Size is 2 bytes.  */
	  /* Mark this instruction.  */
	  code_seq = BR_COND_BR_S256;
	  size = 2;
	  if (optimize)
	    {
	      /* Mark as relaxable.  */
	      RELAX_SET_RELAXABLE (fragP);
	    }
	  else if (optimize_for_space || optimize_for_space_no_align)
	    {
	      /* Mark as relaxed.  */
	      RELAX_SET_RELAXABLE (fragP);
	      RELAX_CLEAR_RELAXED (fragP);
	    }
	}
      else
	{
	  /* 4-byte size.  */
	  size = 4;
	  if (third_higher == BR_RANGE_S64K)
	    {
	      /* beqz rt5, label or other branches.  */
	      code_seq = BR_COND_BR_S64K;
	    }
	  else if (third_higher == BR_RANGE_S16K)
	    {
	      /* beq rt, $lp, label or bne rt, $lp, label  */
	      code_seq = BR_COND_BR_S16K;
	    }
	  else if (third_higher == BR_RANGE_S256)
	    {
	      /* beqc rt, simm11, label or bne rt, simm11, label  */
	      code_seq = BR_COND_BR_S256;
	    }
	}

      break;

    case BR_SEQ_NONE:
    default:
      return 0;
      break;
    }

  if (optimize && RELAX_RELAXABLE (fragP))
    {
      /* This frag is marked as relaxable, save it for later use.  */
      prev_frag = fragP;
    }

  RELAX_SET_FRAG_TC_FLAG (0, fragP, ((RELAX_GET_FRAG_TC_FLAG (0, fragP)
				      & (~RELAX_SEQ_TYPE_MASK))
				     | code_seq << 10));

  /* Return the size difference.  */
  return size - insn_size + adj;
}



/* Estimate the size of load/store instruction sequence.
   fragP: ptr to the target frag.
   segment: segment the frag is in.
   first_time: set to 1 if estimation for the first time else set to 0.
   return value: size difference after estimation.  */

static int
calc_32_to_16_size (fragS *fragP,
		    segT segment ATTRIBUTE_UNUSED, int first_time)
{
  int adj = 0;
  int insn_size;
  int org_size;

  adj = adj_label_pair (fragP);

  if (first_time)
    {
      org_size = 2;
    }
  else
    {
      org_size = RELAX_RELAXED (fragP) ? 4 : 2;
    }

  insn_size = RELAX_RELAXED (fragP) ? 4 : 2;

  return insn_size - org_size + adj;
}

/* Match couple relaxed insn and clear relax.  */

static int
adj_insn16_pair (fragS *fragP)
{
  int adj = 0;
  fixS *fixP;

  /* Try to contract relaxed instruction pair.  */
  if ((fixP = (fixS *) (fragP->tc_frag_data.fixup)))
    {
      /* This frag has label.  */
      while (fixP->tc_fix_data)
	{
	  fixP = (fixS *) fixP->tc_fix_data;
	}

      /* FIXME: Please review this || && expression and add proper parenthesis.  */
      if (fixP && fixP->fx_r_type == BFD_RELOC_NDS32_LABEL
	  && ((fixP->fx_frag->fr_fix > (fixP->fx_where + 1)
	      && 4 == get_frag_insn_size (fixP->fx_frag, fixP->fx_where))
	      || fixP->fx_offset > 1))
	{
	  /* This frag has label; clear previous INSN16.  */
	  prev_insn16 = NULL;
	}
    }

  if (RELAX_RELAXED (fragP))
    {
      /* This frag is relaxed.  */
      if (prev_insn16)
	{
	  RELAX_CLEAR_RELAXED (prev_insn16);
	  RELAX_CLEAR_RELAXED (fragP);

	  /* Now adjust frag address.  */
	  adj_frag_addr (prev_insn16, fragP, -2);
	  adj_frag_addr (fragP, NULL, -4);
	  prev_insn16 = NULL;
	}
      else
	{
	  /* No prev relaxed insn; save it for later used.  */
	  prev_insn16 = fragP;
	}
    }

  return adj;
}

/* Save the relaxable frag in order to align the label.  */

static int
adj_label_pair (fragS *fragP)
{
  fixS *fixP;
  int adj = 0;

  /* Looking for first label in frag.  */
  if (!optimize)
    return 0;

  if ((fixP = (fixS *) (fragP->tc_frag_data.fixup)))
    {
      while (fixP->tc_fix_data)
	{
	  fixP = (fixS *) fixP->tc_fix_data;
	}
      if (fixP && fixP->fx_r_type == BFD_RELOC_NDS32_LABEL
	  && ((fixP->fx_frag->fr_fix > (fixP->fx_where + 1)
	       && 4 == get_frag_insn_size (fixP->fx_frag, fixP->fx_where))
	      || fixP->fx_offset > 1)
	  && prev_frag)
	{
	  if ((fixP->fx_frag->fr_address + fixP->fx_where) & 3)
	    {
	      /* A label is not aligned on boundary and this label has
		 4 byte instruction mark/unmark prev frag, so it will
		 be expanded or contract in next iteration.  */
	      if (RELAX_RELAXED (prev_frag))
		{
		  /* Frag has been expanded; contract it.  */
		  RELAX_CLEAR_RELAXED (prev_frag);
		  adj = -2;
		}
	      else
		{
		  /* Frag has not been expanded; expand it.  */
		  RELAX_SET_RELAXED (prev_frag);
		  adj = 2;
		}

	      /* Now adjust frag address.  */
	      adj_frag_addr (prev_frag, fragP, adj);
	    }
	  prev_frag = NULL;
	}
    }

  /* This frag is relaxable, save it for later use.  */
  if (RELAX_RELAXABLE (fragP))
    prev_frag = fragP;

  return adj;
}

/* Determine prev_frag is valid.  If there is any label between
   current frag and prev_frag, set the prev_frag is invalid.  */

static void
invalid_prev_frag (fragS *fragP)
{
  fragS *frag_t;

  if (!prev_frag)
    return;

  if (prev_frag->last_fr_address >= fragP->last_fr_address)
    {
      prev_frag = NULL;
      return;
    }

  frag_t = prev_frag;
  while (frag_t != fragP)
    {
      if (frag_t->fr_type == rs_align
	  || frag_t->fr_type == rs_align_code
	  || frag_t->fr_type == rs_align_test)
	{
	  /* If there is any alingment between this frag and prev_frag,
	     clear prev_frag, and relax the prev_frag in oder to insert
	     an optional nop if the alignment frag is not aligned.  */
	  if (optimize
	      && (frag_t->fr_address & ((1 << frag_t->fr_offset) - 1))
	      && !RELAX_RELAXED (prev_frag))
	    {
	      RELAX_SET_RELAXED (prev_frag);
	      adj_frag_addr (prev_frag, frag_t, 2);
	    }
	  prev_insn16 = NULL;
	  prev_frag = NULL;
	  return;
	}
      frag_t = frag_t->fr_next;
    }
}

/* md_relax_frag  */

long
nds32_relax_frag (segT segment, fragS *fragP, long stretch ATTRIBUTE_UNUSED)
{
  int adj = 0;

  invalid_prev_frag (fragP);
  adj = adj_insn16_pair (fragP);

  if (RELAX_BRANCH (fragP))
    {
      /* Calculate the final length difference.  */
      return calc_branch_seq_size (fragP, segment, 0, stretch) + adj;
    }
  else if (RELAX_RELAXABLE (fragP))
    {
      /* This 32-bit instruction can be converted to 16-bit.  */
      return calc_32_to_16_size (fragP, segment, 0) + adj;
    }
  else
    {
      return adj_label_pair (fragP) + adj;
    }

  return adj;
}

/* This function returns an initial guess of the length by which a fragment
   must grow to hold a branch to reach its destination.  Also updates
   fr_type/fr_subtype as necessary.

   It is called just before doing relaxation.  Any symbol that is now undefined
   will not become defined.  The guess for fr_var is ACTUALLY the growth beyond
   fr_fix.  Whatever we do to grow fr_fix or fr_var contributes to our returned
   value.  Although it may not be explicit in the frag, pretend fr_var starts
   with a 0 value.  */

int
md_estimate_size_before_relax (fragS *fragP, segT segment)
{
  /* The only thing we have to handle here are symbols outside of the
     current segment.  They may be undefined or in a different segment in
     which case linker scripts may place them anywhere.
     However, we can't finish the fragment here and emit the relocation
     as instruction alignment requirements may move the instruction about.  */
  int adj = 0;

  invalid_prev_frag (fragP);
  adj = adj_insn16_pair (fragP);

  if (RELAX_BRANCH (fragP))
    {
      /* Calculate relax length difference for the first time.  */
      return calc_branch_seq_size (fragP, segment, 1, 0) + adj;
    }
  else if (RELAX_RELAXABLE (fragP))
    {
      /* This 32-bit instruction can be converted to 16-bit.  */
      return calc_32_to_16_size (fragP, segment, 1) + adj;
    }
  else
    {
      return adj_label_pair (fragP) + adj;
    }

  return adj;
}

/* GAS will call this for each rs_machine_dependent fragment.  The instruction
   is completed using the data from the relaxation pass.  It may also create any
   necessary relocations.

   *FRAGP has been relaxed to its final size, and now needs to have the bytes
   inside it modified to conform to the new size.  It is called after relaxation
   is finished.

   fragP->fr_type == rs_machine_dependent.
   fragP->fr_subtype is the subtype of what the address relaxed to.  */

void
md_convert_frag (bfd *abfd ATTRIBUTE_UNUSED, segT sec, fragS *fragP)
{
  int target_address;
  int opcode_address;
  int addend;
  uint32_t insn = 0;
  uint16_t insn16 = 0;
  uint32_t comp_insn = 0;
  uint16_t comp_insn16 = 0;
  unsigned long reloc = 0;
  int org_size = 0;
  int size = 0;
  unsigned long where;
  char *buf;
  expressionS exp, exp_relax, exp_cond;
  fixS *fixP;
  int saved_endian;
  int insn_num;

  if (fragP->fr_symbol == NULL && !RELAX_RELAXABLE (fragP))
    return;

  /* Text is always big endian.  */
  saved_endian = target_big_endian;
  target_big_endian = 1;

  insn_num = RELAX_OPC_NUM (fragP);
  switch (RELAX_OPC_NUM (fragP))
    {
    case NDS32_INSN_MOVI:
    case NDS32_INSN_SETHI:
    case NDS32_INSN_ADDI:
    case NDS32_INSN_ORI:
      org_size = 4;
      break;

    case NDS32_INSN_J:
      insn = INSN_J;
      insn16 = INSN_J8;
      org_size = 4;
      break;

    case NDS32_INSN_JAL:
      insn = INSN_JAL;
      org_size = 4;
      break;

    case NDS32_INSN_JR:
      insn = INSN_JR;
      insn16 = INSN_JR5;
      org_size = 4;
      break;

    case NDS32_INSN_RET:
      insn = INSN_RET;
      insn16 = INSN_RET5;
      org_size = 4;
      break;

    case NDS32_INSN_JRAL:
      insn = INSN_JRAL;
      insn16 = INSN_JRAL5;
      org_size = 4;
      break;

    case NDS32_INSN_BEQZ:
      reloc = BFD_RELOC_NDS32_17_PCREL;
      insn = INSN_BEQZ | (RELAX_RT (fragP) << 20);
      comp_insn = INSN_BNEZ | (RELAX_RT (fragP) << 20);
      if (RELAX_RT (fragP) < REG_R8)
	{
	  insn16 = INSN_BEQZ38 | ((RELAX_RT (fragP) & 0x7) << 8);
	  comp_insn16 = INSN_BNEZ38 | ((RELAX_RT (fragP) & 0x7) << 8);
	}
      else if (RELAX_RT (fragP) == REG_TA)
	{
	  insn16 = INSN_BEQZS8;
	  comp_insn16 = INSN_BNEZS8;
	}

      org_size = 4;
      break;

    case NDS32_INSN_BNEZ:
      reloc = BFD_RELOC_NDS32_17_PCREL;
      insn = INSN_BNEZ | (RELAX_RT (fragP) << 20);
      comp_insn = INSN_BEQZ | (RELAX_RT (fragP) << 20);
      if (RELAX_RT (fragP) < REG_R8)
	{
	  insn16 = INSN_BNEZ38 | ((RELAX_RT (fragP) & 0x7) << 8);
	  comp_insn16 = INSN_BEQZ38 | ((RELAX_RT (fragP) & 0x7) << 8);
	}
      else if (RELAX_RT (fragP) == REG_TA)
	{
	  insn16 = INSN_BNEZS8;
	  comp_insn16 = INSN_BEQZS8;
	}

      org_size = 4;
      break;

    case NDS32_INSN_BGEZ:
      insn = INSN_BGEZ | (RELAX_RT (fragP) << 20);
      comp_insn = INSN_BLTZ | (RELAX_RT (fragP) << 20);
      org_size = 4;
      break;

    case NDS32_INSN_BLTZ:
      insn = INSN_BLTZ | (RELAX_RT (fragP) << 20);
      comp_insn = INSN_BGEZ | (RELAX_RT (fragP) << 20);
      org_size = 4;
      break;

    case NDS32_INSN_BGTZ:
      insn = INSN_BGTZ | (RELAX_RT (fragP) << 20);
      comp_insn = INSN_BLEZ | (RELAX_RT (fragP) << 20);
      org_size = 4;
      break;

    case NDS32_INSN_BLEZ:
      insn = INSN_BLEZ | (RELAX_RT (fragP) << 20);
      comp_insn = INSN_BGTZ | (RELAX_RT (fragP) << 20);
      org_size = 4;
      break;

    case NDS32_INSN_BGEZAL:
      insn = INSN_BGEZAL | (RELAX_RT (fragP) << 20);
      comp_insn = INSN_BLTZ | (RELAX_RT (fragP) << 20);
      org_size = 4;
      break;

    case NDS32_INSN_BLTZAL:
      insn = INSN_BLTZAL | (RELAX_RT (fragP) << 20);
      comp_insn = INSN_BGEZ | (RELAX_RT (fragP) << 20);
      org_size = 4;
      break;

    case NDS32_INSN_BEQ:
      reloc = BFD_RELOC_NDS32_15_PCREL;
      insn = INSN_BEQ | (RELAX_RT (fragP) << 20) | (RELAX_RA (fragP) << 15);
      comp_insn = INSN_BNE | (RELAX_RT (fragP) << 20) | (RELAX_RA (fragP) << 15);
      if (RELAX_RT (fragP) < REG_R8 && RELAX_RA (fragP) == REG_R5
	  && RELAX_RT (fragP) != RELAX_RA (fragP))
	{
	  insn16 = INSN_BEQS38 | ((RELAX_RT (fragP) & 0x7) << 8);
	  comp_insn16 = INSN_BNES38 | ((RELAX_RT (fragP) & 0x7) << 8);
	}
      else if (RELAX_RA (fragP) < REG_R8 && RELAX_RT (fragP) == REG_R5
	       && RELAX_RT (fragP) != RELAX_RA (fragP))
	{
	  insn16 = INSN_BEQS38 | ((RELAX_RA (fragP) & 0x7) << 8);
	  comp_insn16 = INSN_BNES38 | ((RELAX_RA (fragP) & 0x7) << 8);
	}
      org_size = 4;
      break;

    case NDS32_INSN_BNE:
      reloc = BFD_RELOC_NDS32_15_PCREL;
      insn = INSN_BNE | (RELAX_RT (fragP) << 20) | (RELAX_RA (fragP) << 15);
      comp_insn = INSN_BEQ | (RELAX_RT (fragP) << 20)
		  | (RELAX_RA (fragP) << 15);
      if (RELAX_RT (fragP) < REG_R8 && RELAX_RA (fragP) == REG_R5
	  && RELAX_RT (fragP) != RELAX_RA (fragP))
	{
	  insn16 = INSN_BNES38 | ((RELAX_RT (fragP) & 0x7) << 8);
	  comp_insn16 = INSN_BEQS38 | ((RELAX_RT (fragP) & 0x7) << 8);
	}
      else if (RELAX_RA (fragP) < REG_R8 && RELAX_RT (fragP) == REG_R5
	       && RELAX_RT (fragP) != RELAX_RA (fragP))
	{
	  insn16 = INSN_BNES38 | ((RELAX_RA (fragP) & 0x7) << 8);
	  comp_insn16 = INSN_BEQS38 | ((RELAX_RA (fragP) & 0x7) << 8);
	}
      org_size = 4;
      break;

    case NDS32_INSN_BEQC:
      reloc = BFD_RELOC_NDS32_WORD_9_PCREL;
      insn = N32_BR3 (BEQC, RELAX_RT (fragP), RELAX_SIMM11 (fragP), 0);
      if (RELAX_SEQ_TYPE (fragP) == BR_COND_BR_S16K
	  && RELAX_SIMM11 (fragP) < 16 && RELAX_SIMM11 (fragP) >= -16)
	{
	  comp_insn16 = N16_TYPE55 (MOVI55, REG_R15, RELAX_SIMM11 (fragP));
	  comp_insn = N32_BR1 (BEQ, RELAX_RT (fragP), REG_R15, 0);
	}
      else
	comp_insn = N32_BR3 (BNEC, RELAX_RT (fragP), RELAX_SIMM11 (fragP), 0);
      org_size = 4;
      break;

    case NDS32_INSN_BNEC:
      reloc = BFD_RELOC_NDS32_WORD_9_PCREL;
      insn = N32_BR3 (BNEC, RELAX_RT (fragP), RELAX_SIMM11 (fragP), 0);
      if (RELAX_SEQ_TYPE (fragP) == BR_COND_BR_S16K
	  && RELAX_SIMM11 (fragP) < 16 && RELAX_SIMM11 (fragP) >= -16)
	{
	  comp_insn16 = N16_TYPE55 (MOVI55, REG_R15, RELAX_SIMM11 (fragP));
	  comp_insn = N32_BR1 (BNE, RELAX_RT (fragP), REG_R15, 0);
	}
      else
	comp_insn = N32_BR3 (BEQC, RELAX_RT (fragP), RELAX_SIMM11 (fragP), 0);
      org_size = 4;
      break;

    case NDS32_INSN_J8:
      insn16 = INSN_J8;
      insn = INSN_J;
      org_size = 2;
      break;

    case NDS32_INSN_JR5:
      insn16 = INSN_JR5;
      insn = INSN_JR;
      org_size = 2;
      break;

    case NDS32_INSN_RET5:
      insn16 = INSN_RET5;
      insn = INSN_RET;
      org_size = 2;
      break;

    case NDS32_INSN_JRAL5:
      insn16 = INSN_JRAL5;
      insn = INSN_JRAL;
      org_size = 2;
      break;

    case NDS32_INSN_BEQZ38:
      reloc = BFD_RELOC_NDS32_17_PCREL;
      comp_insn16 = INSN_BNEZ38 | ((RELAX_RT (fragP) & 0x7) << 8);
      insn16 = INSN_BEQZ38 | ((RELAX_RT (fragP) & 0x7) << 8);
      comp_insn = INSN_BNEZ | (RELAX_RT (fragP) << 20);
      insn = INSN_BEQZ | (RELAX_RT (fragP) << 20);
      org_size = 2;
      break;

    case NDS32_INSN_BNEZ38:
      reloc = BFD_RELOC_NDS32_17_PCREL;
      comp_insn16 = INSN_BEQZ38 | ((RELAX_RT (fragP) & 0x7) << 8);
      insn16 = INSN_BNEZ38 | ((RELAX_RT (fragP) & 0x7) << 8);
      comp_insn = INSN_BEQZ | (RELAX_RT (fragP) << 20);
      insn = INSN_BNEZ | (RELAX_RT (fragP) << 20);
      org_size = 2;
      break;

    case NDS32_INSN_BEQS38:
      reloc = BFD_RELOC_NDS32_15_PCREL;
      comp_insn16 = INSN_BNES38 | ((RELAX_RT (fragP) & 0x7) << 8);
      insn16 = INSN_BEQS38 | ((RELAX_RT (fragP) & 0x7) << 8);
      comp_insn = INSN_BNE | (RELAX_RT (fragP) << 20) | (REG_R5 << 15);
      insn = INSN_BEQ | (RELAX_RT (fragP) << 20) | (REG_R5 << 15);
      org_size = 2;
      break;

    case NDS32_INSN_BNES38:
      reloc = BFD_RELOC_NDS32_15_PCREL;
      comp_insn16 = INSN_BEQS38 | ((RELAX_RT (fragP) & 0x7) << 8);
      insn16 = INSN_BNES38 | ((RELAX_RT (fragP) & 0x7) << 8);
      comp_insn = INSN_BEQ | (RELAX_RT (fragP) << 20) | (REG_R5 << 15);
      insn = INSN_BNE | (RELAX_RT (fragP) << 20) | (REG_R5 << 15);
      org_size = 2;
      break;

    case NDS32_INSN_BEQZS8:
      reloc = BFD_RELOC_NDS32_17_PCREL;
      comp_insn16 = INSN_BNEZS8;
      insn16 = INSN_BEQZS8;
      comp_insn = INSN_BNEZ | (REG_R15 << 20);
      insn = INSN_BEQZ | (REG_R15 << 20);
      org_size = 2;
      break;

    case NDS32_INSN_BNEZS8:
      reloc = BFD_RELOC_NDS32_17_PCREL;
      comp_insn16 = INSN_BEQZS8;
      insn16 = INSN_BNEZS8;
      comp_insn = INSN_BEQZ | (REG_R15 << 20);
      insn = INSN_BNEZ | (REG_R15 << 20);
      org_size = 2;
      break;

    case NDS32_INSN_IFRET:
      insn16 = ((*(fragP->fr_literal + fragP->fr_fix - 2) & 0xff) << 8)
	       | (*(fragP->fr_literal + fragP->fr_fix - 1) & 0xff);

      /* Check if current instruction is IFRET16.   */
      if (insn16 == INSN_IFRET16)
	/* IFRET16  */
	org_size = 2;
      else
	/* IFRET  */
	org_size = 4;
	/* insn = INSN_IFRET;  */
	/* insn16 = INSN_IFRET16;  */
      break;

    case NDS32_INSN_BMSKI33:
    case NDS32_INSN_FEXTI33:
    case NDS32_INSN_AND33:
    case NDS32_INSN_OR33:
    case NDS32_INSN_XOR33:
    case NDS32_INSN_MUL33:
    case NDS32_INSN_NOT33:
    case NDS32_INSN_NEG33:
    case NDS32_INSN_ADDRI36_SP:
    case NDS32_INSN_MOVPI45:

    case NDS32_INSN_MOV55:
    case NDS32_INSN_MOVI55:
    case NDS32_INSN_ADDI45:
    case NDS32_INSN_ADD45:
    case NDS32_INSN_SUBI45:
    case NDS32_INSN_SUB45:
    case NDS32_INSN_SRAI45:
    case NDS32_INSN_SRLI45:
    case NDS32_INSN_SLLI333:
    case NDS32_INSN_SEB33:
    case NDS32_INSN_SEH33:
    case NDS32_INSN_ZEB33:
    case NDS32_INSN_ZEH33:
    case NDS32_INSN_XLSB33:
    case NDS32_INSN_X11B33:
    case NDS32_INSN_ADDI333:
    case NDS32_INSN_ADD333:
    case NDS32_INSN_SUBI333:
    case NDS32_INSN_SUB333:
    case NDS32_INSN_LWI333:
    case NDS32_INSN_LWI333_BI:
    case NDS32_INSN_LHI333:
    case NDS32_INSN_LBI333:
    case NDS32_INSN_SWI333:
    case NDS32_INSN_SWI333_BI:
    case NDS32_INSN_SHI333:
    case NDS32_INSN_SBI333:
    case NDS32_INSN_LWI450:
    case NDS32_INSN_SWI450:
    case NDS32_INSN_LWI37:
    case NDS32_INSN_SWI37:
    case NDS32_INSN_SLTI45:
    case NDS32_INSN_SLTSI45:
    case NDS32_INSN_SLT45:
    case NDS32_INSN_SLTS45:
    case NDS32_INSN_BREAK16:
    case NDS32_INSN_ADDI10_SP:
    case NDS32_INSN_LWI37_SP:
    case NDS32_INSN_SWI37_SP:
      org_size = 2;
      break;

    default:
      org_size = 4;
      break;
    }

  buf = fragP->fr_literal + fragP->fr_fix - org_size;
  where = fragP->fr_fix - org_size;

  /* We have final code sequence for relaxable object, expand it now.  */
  if (RELAX_BRANCH (fragP))
    {

      if (S_GET_SEGMENT (fragP->fr_symbol) != sec
	  || S_IS_WEAK (fragP->fr_symbol))
	{
	  /* Symbol must be resolved by linker.  */
	  if (fragP->fr_offset & 3)
	    as_warn (_("Addend to unresolved symbol not on word boundary."));
	  addend = 0;
	  exp.X_op = O_symbol;
	  exp.X_add_symbol = fragP->fr_symbol;
	  exp.X_add_number = fragP->fr_offset;
	}
      else
	{
	  /* Address we want to reach in file space.  */
	  opcode_address = fragP->fr_address + fragP->fr_fix - org_size;
	  target_address = S_GET_VALUE (fragP->fr_symbol) + fragP->fr_offset;
	  addend = (target_address - (opcode_address & -2)) >> 1;

	  /* Symbol_get_value_expression ??  */
	  exp.X_op = O_symbol;
	  exp.X_add_symbol = fragP->fr_symbol;
	  exp.X_add_number = fragP->fr_offset;
	}

      switch (RELAX_SEQ_TYPE (fragP))
	{
	case BR_UCOND_CALL_S16M:
	  /* jal   label ; 25_PCREL
	     Instruction does not change.
	     Just fill in the addend.
	     Symbol has been resolved.  */

	  /* ET - TBI: assume code is within +/-16M, we should handle.  */
	  /* Enlarger the range later.  */
	  insn = INSN_JAL;
	  md_number_to_chars (buf, insn, 4);
	  if (pic_code && (S_GET_SEGMENT (fragP->fr_symbol) != sec
			   || S_IS_WEAK (fragP->fr_symbol)))
	    fixP = fix_new_exp (fragP, where, 4, &exp, 0,
			   BFD_RELOC_NDS32_25_PLTREL);
	  else
	    fixP = fix_new_exp (fragP, where, 4, &exp, 0,
			   BFD_RELOC_NDS32_25_PCREL);
	  fixP->fx_addnumber = fixP->fx_offset;
	  size = 4;
	  break;

	case BR_UCOND_CALL_U4G:
	  if (pic_code && (S_GET_SEGMENT (fragP->fr_symbol) != sec
			   || S_IS_WEAK (fragP->fr_symbol)))
	    {
	      /* sethi $ta, hi20(label)       ; PLT_HI20
		 ori   $ta, $ta, lo20(label)  ; PLT_LO12/PTR/PTRCOUNT
		 add   $ta, $ta, $gp          ; PTR/PTRCOUT
		 jral  $ta or jral5 $ta       ; PLT_GOT_SUFF (INSN16)  */

	      /* Create sethi.  */
	      insn = INSN_SETHI_TA;
	      md_number_to_chars (buf, insn, 4);
	      fixP = fix_new_exp (fragP, where, 4, &exp, 0,
			     BFD_RELOC_NDS32_PLT_GOTREL_HI20);
	      fixP->fx_addnumber = fixP->fx_offset;

	      /* Create ori.  */
	      insn = INSN_ORI_TA;
	      md_number_to_chars (buf + 4, insn, 4);
	      fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			     BFD_RELOC_NDS32_PLT_GOTREL_LO12);
	      fixP->fx_addnumber = fixP->fx_offset;

	      insn = INSN_ADD_TA | (REG_TA << 15 | REG_GP << 10);
	      md_number_to_chars (buf + 8, insn, 4);

	      insn = INSN_JRAL_TA;
	      md_number_to_chars (buf + 12, insn, 4);
	      size = 16;
	      if (!RELAX_USE_32BIT (fragP) && optimize && enable_relax_relocs)
		{
		  /* Optimize for speed, use jral because next instruction is
		     return address which has a implicit label
		     Insert INSN16 reloc, so we can contract it to align next
		     label if necessary.  */
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = 0;
		  fix_new_exp (fragP, where + 8, 4, &exp_relax, 0,
			       BFD_RELOC_NDS32_INSN16);
		  fix_new_exp (fragP, where + 12, 4, &exp_relax, 0,
			       BFD_RELOC_NDS32_INSN16);
		}

	      if (enable_relax_relocs)
		{
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = SET_ADDEND (size, is_convertible (fragP),
				optimize, !RELAX_USE_32BIT (fragP));
		  fix_new_exp (fragP, where, size, &exp_relax, 0,
			       BFD_RELOC_NDS32_PLTBLOCK);
		}
	    }
	  else
	    {
	      /* sethi $ta, hi20(label)       ; LONGCALL1/HI20
		 ori   $ta, $ta, lo20(label)  ; LO12S0
		 jral  $ta or jral5 $ta       ; (INSN16)  */

	      /* gas_assert (RELAX_OPC_NUM(fragP->fr_subtype) == NDS32_INSN_JAL );  */

	      /* Create sethi.  */
	      insn = INSN_SETHI_TA;
	      md_number_to_chars (buf, insn, 4);
	      fixP = fix_new_exp (fragP, where, 4, &exp, 0, BFD_RELOC_NDS32_HI20);
	      fixP->fx_addnumber = fixP->fx_offset;

	      /* Create ori.  */
	      insn = INSN_ORI_TA;
	      md_number_to_chars (buf + 4, insn, 4);
	      if (enable_relax_relocs)
		fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			       BFD_RELOC_NDS32_LO12S0_ORI);
	      else
		fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			       BFD_RELOC_NDS32_LO12S0);
	      fixP->fx_addnumber = fixP->fx_offset;

	      if (RELAX_USE_32BIT (fragP) || optimize)
		{
		  insn = INSN_JRAL_TA;
		  md_number_to_chars (buf + 8, insn, 4);
		  size = 12;
		  if (!RELAX_USE_32BIT (fragP) && optimize
		      && enable_relax_relocs)
		    {
		      /* Optimize for speed, use jral because next instruction
			  is return address which has a implicit label
			 Insert INSN16 reloc, so we can contract it to align next
			 label if necessary.  */
		      exp_relax.X_op = O_symbol;
		      exp_relax.X_add_symbol = abs_section_sym;
		      exp_relax.X_add_number = 0;
		      fix_new_exp (fragP, where + 8, 4, &exp_relax, 0,
				   BFD_RELOC_NDS32_INSN16);
		    }
		}
	      else
		{
		  /* Use jral5 for smaller code size.  */
		  insn16 = INSN_JRAL5_TA;
		  md_number_to_chars (buf + 8, insn16, 2);
		  size = 10;
		}

	      /* Create a reloc for this sequence, so linker can contract
		 it to smaller size.  The register $ta may be used by callee
		 to to calculate $gp this optimization needs further investigation.  */
	      if (enable_relax_relocs)
		{
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = SET_ADDEND (size, is_convertible (fragP),
				optimize, !RELAX_USE_32BIT (fragP));
		  fix_new_exp (fragP, where, size, &exp_relax, 0,
			       BFD_RELOC_NDS32_LONGCALL1);
		}
	    }
	  break;

	case BR_COND_CALL_S64K:
	  /* `bgezal rt, label' or `bltzal rt, label' 17_PCREL
	     0x0e0c0000 | (reg << 20)
	     0x0e0d0000 | (reg << 20)
	     Instruction does not change.
	     Symbol has been resolved, no reloc is needed.
	     Just fill in the addend.  */

	  insn |= (RELAX_RT (fragP) << 20);
	  md_number_to_chars (buf, insn, 4);

	  fixP = fix_new_exp (fragP, where, 4, &exp, 0, BFD_RELOC_NDS32_17_PCREL);
	  fixP->fx_addnumber = fixP->fx_offset;
	  size = 4;
	  break;

	case BR_COND_CALL_S16M:
	  /* bltz  rt, $1 or bgez  rt, $1 ; LONGCALL2
	     jal   label    ; 25_PCREL
	     $1:  */

	  comp_insn |= (RELAX_RT (fragP) << 20);
	  md_number_to_chars (buf, comp_insn, 4);
	  exp_cond.X_op = O_symbol;
	  exp_cond.X_add_symbol = symbol_temp_new (sec, 0, fragP->fr_next);
	  exp_cond.X_add_number = 0;
	  fix_new_exp (fragP, where, 4, &exp_cond, 0,
		       BFD_RELOC_NDS32_17_PCREL);

	  /* Create jal.  */
	  /* ET - TBI: assume code is within +/-16M, we should handle.  */
	  /* Larger range later.  */
	  insn = INSN_JAL;
	  md_number_to_chars (buf + 4, insn, 4);
	  if (pic_code && (S_GET_SEGMENT (fragP->fr_symbol) != sec
			   || S_IS_WEAK (fragP->fr_symbol)))
	    fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			   BFD_RELOC_NDS32_25_PLTREL);
	  else
	    fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			   BFD_RELOC_NDS32_25_PCREL);
	  fixP->fx_addnumber = fixP->fx_offset;
	  size = 8;

	  if (enable_relax_relocs)
	    {
	      exp_relax.X_op = O_symbol;
	      exp_relax.X_add_symbol = abs_section_sym;
	      exp_relax.X_add_number = SET_ADDEND (8, is_convertible (fragP),
			    optimize, !RELAX_USE_32BIT (fragP));
	      fix_new_exp (fragP, where, 8, &exp_relax, 0,
			   BFD_RELOC_NDS32_LONGCALL2);
	    }

	  break;

	case BR_COND_CALL_U4G:
	  /* bltz  rt, $1 or bgez  rt,   $1 ; LONGCALL3
	     sethi $ta, hi20(label)     ; HI20
	     ori   $ta, $ta, lo12(label)  ; LO12S0
	     jral  $ta or jral5 $ta       ; (INSN16)
	     $1:  */

	  comp_insn |= (RELAX_RT (fragP) << 20);
	  md_number_to_chars (buf, comp_insn, 4);
	  exp_cond.X_op = O_symbol;
	  exp_cond.X_add_symbol = symbol_temp_new (sec, 0, fragP->fr_next);
	  exp_cond.X_add_number = 0;
	  fix_new_exp (fragP, where, 4, &exp_cond, 0,
		       BFD_RELOC_NDS32_17_PCREL);

	  if (pic_code && (S_GET_SEGMENT (fragP->fr_symbol) != sec
			   || S_IS_WEAK (fragP->fr_symbol)))
	    {
	      /* Create sethi.  */
	      insn = INSN_SETHI_TA;
	      md_number_to_chars (buf + 4, insn, 4);
	      fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			     BFD_RELOC_NDS32_PLT_GOTREL_HI20);
	      fixP->fx_addnumber = fixP->fx_offset;

	      /* Create ori.  */
	      insn = INSN_ORI_TA;
	      md_number_to_chars (buf + 8, insn, 4);
	      fixP = fix_new_exp (fragP, where + 8, 4, &exp, 0,
			     BFD_RELOC_NDS32_PLT_GOTREL_LO12);
	      fixP->fx_addnumber = fixP->fx_offset;

	      insn = INSN_ADD_TA | (REG_TA << 15 | REG_GP << 10);
	      md_number_to_chars (buf + 12, insn, 4);

	      insn = INSN_JRAL_TA;
	      md_number_to_chars (buf + 16, insn, 4);
	      size = 16;
	      if (!RELAX_USE_32BIT (fragP) && optimize && enable_relax_relocs)
		{
		  /* Optimize for speed, use jral because next instruction is
		     return address which has a implicit label.
		     Insert 16-bit instruction fixup, so we can contract it to
		     align next label if necessary.  */
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = 0;
		  fix_new_exp (fragP, where + 12, 4, &exp_relax, 0,
			       BFD_RELOC_NDS32_INSN16);
		  fix_new_exp (fragP, where + 16, 4, &exp_relax, 0,
			       BFD_RELOC_NDS32_INSN16);
		}

	      /* Create a reloc for this sequence, so linker can contract
		 it to smaller size.  */
	      if (enable_relax_relocs)
		{
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = SET_ADDEND (size, is_convertible (fragP),
				optimize, !RELAX_USE_32BIT (fragP));
		  fix_new_exp (fragP, where + 4, size, &exp_relax, 0,
			       BFD_RELOC_NDS32_PLTBLOCK);
		}
	    }
	  else
	    {
	      /* Create sethi.  */
	      insn = INSN_SETHI_TA;
	      md_number_to_chars (buf + 4, insn, 4);

	      fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			     BFD_RELOC_NDS32_HI20);
	      fixP->fx_addnumber = fixP->fx_offset;

	      /* Create ori.  */
	      insn = INSN_ORI_TA;
	      md_number_to_chars (buf + 8, insn, 4);

	      if (enable_relax_relocs)
		fixP = fix_new_exp (fragP, where + 8, 4, &exp, 0,
			       BFD_RELOC_NDS32_LO12S0_ORI);
	      else
		fixP = fix_new_exp (fragP, where + 8, 4, &exp, 0,
			       BFD_RELOC_NDS32_LO12S0);
	      fixP->fx_addnumber = fixP->fx_offset;

	      /* Create jral(5).  */
	      if (RELAX_USE_32BIT (fragP) || optimize)
		{
		  insn = INSN_JRAL_TA;
		  md_number_to_chars (buf + 12, insn, 4);
		  size = 16;
		  if (!RELAX_USE_32BIT (fragP) && optimize
		      && enable_relax_relocs)
		    {
		      /* Optimize for speed, use jral because next instruction
			 is return address which has a implicit label.
			 Insert 16-bit instruction fixup, so we can contract it
			 to align next label if necessary.  */
		      exp_relax.X_op = O_symbol;
		      exp_relax.X_add_symbol = abs_section_sym;
		      exp_relax.X_add_number = 0;
		      fix_new_exp (fragP, where + 12, 4, &exp_relax, 0,
				   BFD_RELOC_NDS32_INSN16);
		    }
		}
	      else
		{
		  /* Use jral5 for smaller code size.  */
		  insn16 = INSN_JRAL5_TA;
		  md_number_to_chars (buf + 12, insn16, 2);
		  size = 14;
		}

	      /* Create a reloc for this sequence, so linker can contract
		 it to smaller size.  */
	      if (enable_relax_relocs)
		{
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = SET_ADDEND (size, is_convertible (fragP),
				optimize, !RELAX_USE_32BIT (fragP));
		  fix_new_exp (fragP, where, size, &exp_relax, 0,
			       BFD_RELOC_NDS32_LONGCALL3);
		}
	    }
	  break;

	case BR_UCOND_BR_S256:
	  /* j8    label  */

	  if (optimize && RELAX_RELAXED (fragP))
	    {
	      if (!RELAX_USE_32BIT (fragP)
		  && optimize && addend >= -0x80 && addend < 0x80
		  && enable_relax_relocs)
		{
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = 0;
		  fix_new_exp (fragP, where, 4, &exp_relax, 0,
			       BFD_RELOC_NDS32_INSN16);
		}

	      insn = INSN_J;
	      md_number_to_chars (buf, insn, 4);
	      fixP = fix_new_exp (fragP, where, 4, &exp, 0,
			     BFD_RELOC_NDS32_25_PCREL);
	      fixP->fx_addnumber = fixP->fx_offset;
	      size = 4;
	    }
	  else
	    {
	      insn16 = INSN_J8;
	      md_number_to_chars (buf, insn16, 2);
	      fixP = fix_new_exp (fragP, where, 2, &exp, 0,
			     BFD_RELOC_NDS32_9_PCREL);
	      fixP->fx_addnumber = fixP->fx_offset;
	      /* The addend is not embedded in the instruction,
		 the test of overflow can be passed.  */
	      fixP->fx_no_overflow = 1;
	      size = 2;
	    }
	  break;

	case BR_UCOND_BR_S16M:
	  /* j     label    ; 25_PCREL/INSN16  */

	  if (RELAX_RELAXABLE (fragP) && RELAX_RELAXED (fragP)
	      && enable_relax_relocs)
	    {
	      exp.X_op = O_symbol;
	      exp.X_add_symbol = abs_section_sym;
	      exp.X_add_number = 0;
	      fix_new_exp (fragP, where, 4, &exp, 0, BFD_RELOC_NDS32_INSN16);
	    }
	  /* ET - TBI: assume code is within +/-16M, we should handle.  */
	  /* Larger range later.  */
	  insn = INSN_J;
	  md_number_to_chars (buf, insn, 4);
	  if (pic_code && (S_GET_SEGMENT (fragP->fr_symbol) != sec
			   || S_IS_WEAK (fragP->fr_symbol)))
	    fixP = fix_new_exp (fragP, where, 4, &exp, 0,
			   BFD_RELOC_NDS32_25_PLTREL);
	  else
	    fixP = fix_new_exp (fragP, where, 4, &exp, 0,
			   BFD_RELOC_NDS32_25_PCREL);
	  fixP->fx_addnumber = fixP->fx_offset;
	  size = 4;
	  break;

	case BR_UCOND_BR_U4G:
	  /* sethi $ta, hi20(label)       ; LONGJUMP1/HI20
	     ori   $ta, $ta, lo12(label)  ; LO12S0
	     jr    $ta or jr5   $ta       ; (INSN16)  */

	  /* Create sethi.  */
	  insn = INSN_SETHI_TA;
	  md_number_to_chars (buf, insn, 4);
	  fixP = fix_new_exp (fragP, where, 4, &exp, 0, BFD_RELOC_NDS32_HI20);
	  fixP->fx_addnumber = fixP->fx_offset;

	  /* Create ori.  */
	  insn = INSN_ORI_TA;
	  md_number_to_chars (buf + 4, insn, 4);
	  if (enable_relax_relocs)
	    fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			   BFD_RELOC_NDS32_LO12S0_ORI);
	  else
	    fixP = fix_new_exp (fragP, where + 4, 4, &exp, 0,
			   BFD_RELOC_NDS32_LO12S0);
	  fixP->fx_addnumber = fixP->fx_offset;

	  if (RELAX_USE_32BIT (fragP) || optimize)
	    {
	      insn = INSN_JR_TA;
	      md_number_to_chars (buf + 8, insn, 4);
	      size = 12;
	      if (!RELAX_USE_32BIT (fragP) && optimize && enable_relax_relocs)
		{
		  /* Optimize for speed, use jral because next instruction is
		     return address which has a implicit label.

		     Instruct 16-bit instruction fixup, so we can contract it
		     to align next label if necessary. Save fixup info for later
		     BFD_RELOC_NDS32_LABEL.  */
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = 0;
		  fix_new_exp (fragP, where + 8, 4, &exp_relax, 0,
			       BFD_RELOC_NDS32_INSN16);
		}
	    }
	  else
	    {
	      /* Use jr5 for smaller code size.  */
	      insn16 = INSN_JR5_TA;
	      md_number_to_chars (buf + 8, insn16, 2);
	      size = 10;
	    }

	  /* Create a relocation for this sequence, so linker can contract
	     it to smaller size.  */
	  if (enable_relax_relocs)
	    {
	      exp_relax.X_op = O_symbol;
	      exp_relax.X_add_symbol = abs_section_sym;
	      exp_relax.X_add_number = SET_ADDEND (size, is_convertible (fragP),
			    optimize, !RELAX_USE_32BIT (fragP));
	      fix_new_exp (fragP, where, size, &exp_relax, 0,
			   BFD_RELOC_NDS32_LONGJUMP1);
	    }
	  break;

	case BR_COND_BR_S256:
	  /* beqs38 rt3,  label or other 16-bit branch.  */

	  if (insn_num == NDS32_INSN_BEQC || insn_num == NDS32_INSN_BNEC)
	    {
	      /* beqc/bnec  */
	      fixP = fix_new_exp (fragP, where, 4, &exp, 0, reloc);
	      fixP->fx_addnumber = fixP->fx_offset;
	      md_number_to_chars (buf, insn, 4);
	      size = 4;
	    }
	  else if (optimize && RELAX_RELAXED (fragP))
	    {
	      if (!RELAX_USE_32BIT (fragP) && optimize
		  && addend >= -0x80 && addend < 0x80 && enable_relax_relocs)
		{
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = 0;
		  fix_new_exp (fragP, where, 4, &exp_relax, 0,
			       BFD_RELOC_NDS32_INSN16);
		}
	      fixP = fix_new_exp (fragP, where, 4, &exp, 0, reloc);
	      fixP->fx_addnumber = fixP->fx_offset;
	      if (reloc == BFD_RELOC_NDS32_9_PCREL)
		fixP->fx_no_overflow = 1;
	      md_number_to_chars (buf, insn, 4);
	      size = 4;
	    }
	  else
	    {
	      md_number_to_chars (buf, insn16, 2);
	      size = 2;
	      /* The addend is not embedded in the instruction,
		 the test of overflow can be passed.  */
	      fixP = fix_new_exp (fragP, where, 2, &exp, 0,
			     BFD_RELOC_NDS32_9_PCREL);
	      fixP->fx_addnumber = fixP->fx_offset;
	      fixP->fx_no_overflow = 1;
	    }
	  break;

	case BR_COND_BR_S16K:
	  /* beq   label or bne   label  */
	  if (insn_num == NDS32_INSN_BEQC || insn_num == NDS32_INSN_BNEC)
	    {
	      size=2;
	      md_number_to_chars (buf, comp_insn16, 2);
	      addend -= 1;
	      md_number_to_chars (buf+size, comp_insn, 4);
	      fixP = fix_new_exp (fragP, where+2, 4, &exp, 0, BFD_RELOC_NDS32_15_PCREL);
	      fixP->fx_addnumber = fixP->fx_offset;

	      /* 16-bit instruction fixup,
		 so we can expand it to align next label if necessary.  */
	      size += 4;
	      break;
	    }
	  md_number_to_chars (buf, insn, 4);
	  fixP = fix_new_exp (fragP, where, 4, &exp, 0, BFD_RELOC_NDS32_15_PCREL);
	  fixP->fx_addnumber = fixP->fx_offset;

	  /* 16-bit instruction fixup, so we can expand it to align next
	     label if necessary.  */
	  if ((optimize || optimize_for_space || optimize_for_space_no_align)
	      && is_convertible (fragP) && enable_relax_relocs)
	    {
	      exp.X_op = O_symbol;
	      exp.X_add_symbol = abs_section_sym;
	      exp.X_add_number = 0;
	      fix_new_exp (fragP, where, 4, &exp, 0, BFD_RELOC_NDS32_INSN16);
	    }

	  size = 4;
	  break;

	case BR_COND_BR_S64K:
	  /* 32-bit branch instructions except bne or beq.  */

	  md_number_to_chars (buf, insn, 4);

	  fixP = fix_new_exp (fragP, where, 4, &exp, 0, BFD_RELOC_NDS32_17_PCREL);
	  fixP->fx_addnumber = fixP->fx_offset;

	  if (!RELAX_USE_32BIT (fragP)
	      && is_convertible (fragP) && enable_relax_relocs)
	    {
	      exp_relax.X_op = O_symbol;
	      exp_relax.X_add_symbol = abs_section_sym;
	      exp_relax.X_add_number = 0;
	      fix_new_exp (fragP, where, 4, &exp_relax, 0,
			   BFD_RELOC_NDS32_INSN16);
	    }

	  size = 4;
	  break;

	case BR_COND_BR_S16M:
	  /* bne  $1     ; LONGJUMP2/(INSN16)
	     j     label ; 25_PCREL
	     $1:         ; (LABEL)
	     Use 32-bit complimentary branch.  */

	  if (insn_num == NDS32_INSN_BEQC || insn_num == NDS32_INSN_BNEC)
	    {
	      /* beqc/bnec  */
	      size = 4;
	      md_number_to_chars (buf, comp_insn, 4);
	      exp_cond.X_op = O_symbol;
	      exp_cond.X_add_symbol = symbol_temp_new (sec, 0, fragP->fr_next);
	      exp_cond.X_add_number = 0;

	      fix_new_exp (fragP, where, 4, &exp_cond, 0,
			   BFD_RELOC_NDS32_WORD_9_PCREL);
	      addend -= 2;
	    }
	  /* Set proper relocation type.  */
	  else if (RELAX_USE_32BIT (fragP) || optimize
		   || !is_convertible (fragP))
	    {
	      size = 4;
	      /* Add branch offset.  */
	      md_number_to_chars (buf, comp_insn, 4);
	      exp_cond.X_op = O_symbol;
	      exp_cond.X_add_symbol = symbol_temp_new (sec, 0, fragP->fr_next);
	      exp_cond.X_add_number = 0;

	      fix_new_exp (fragP, where, 4, &exp_cond, 0,
			   BFD_RELOC_NDS32_15_PCREL);
	      addend -= 2;

	      if (!RELAX_USE_32BIT (fragP) && optimize)
		{
		  if (is_convertible (fragP) && enable_relax_relocs)
		    {
		      exp_relax.X_op = O_symbol;
		      exp_relax.X_add_symbol = abs_section_sym;
		      exp_relax.X_add_number = 0;
		      fix_new_exp (fragP, where, 4, &exp_relax, 0,
				   BFD_RELOC_NDS32_INSN16);
		    }
		}
	    }
	  else
	    {
	      size = 2;
	      /* Add branch offset.  */
	      md_number_to_chars (buf, comp_insn16, 2);
	      exp_cond.X_op = O_symbol;
	      exp_cond.X_add_symbol = symbol_temp_new (sec, 0, fragP->fr_next);
	      exp_cond.X_add_number = 0;
	      fixP = fix_new_exp (fragP, where, 2, &exp_cond, 0,
			     BFD_RELOC_NDS32_9_PCREL);
	      fixP->fx_no_overflow = 1;
	      addend -= 1;
	    }

	  /* Create j.  */
	  insn = INSN_J;
	  md_number_to_chars (buf + size, insn, 4);
	  if (pic_code && (S_GET_SEGMENT (fragP->fr_symbol) != sec
			   || S_IS_WEAK (fragP->fr_symbol)))
	    fixP = fix_new_exp (fragP, where + size, 4, &exp, 0,
			   BFD_RELOC_NDS32_25_PLTREL);
	  else
	    fixP = fix_new_exp (fragP, where + size, 4, &exp, 0,
			   BFD_RELOC_NDS32_25_PCREL);
	  fixP->fx_addnumber = fixP->fx_offset;
	  size += 4;

	  /* Create a relocation for this sequence, so linker can contract
	     it to smaller size.  */
	  if (enable_relax_relocs
	      && !(insn_num == NDS32_INSN_BEQC
		   || insn_num == NDS32_INSN_BNEC))
	    {
	      exp_relax.X_op = O_symbol;
	      exp_relax.X_add_symbol = abs_section_sym;
	      exp_relax.X_add_number = SET_ADDEND (size, is_convertible (fragP),
			    optimize, !RELAX_USE_32BIT (fragP));
	      fix_new_exp (fragP, where, size, &exp_relax, 0,
			   BFD_RELOC_NDS32_LONGJUMP2);
	    }
	  break;

	case BR_COND_BR_U4G:
	  /* bnes38   $1                   ; or bne   $1
	     sethi    $ta, hi20(label)
	     ori      $ta, $ta, lo12(label)
	     jr5      $ta                   ; or jr $ta
	     $1:  */

	  if (insn_num == NDS32_INSN_BEQC || insn_num == NDS32_INSN_BNEC)
	    {
	      /* beqc/bnec  */
	      size = 4;
	      md_number_to_chars (buf, comp_insn, 4);
	      exp_cond.X_op = O_symbol;
	      exp_cond.X_add_symbol = symbol_temp_new (sec, 0, fragP->fr_next);
	      exp_cond.X_add_number = 0;
	      fix_new_exp (fragP, where, 4, &exp_cond, 0,
			   BFD_RELOC_NDS32_WORD_9_PCREL);

	    }
	  if (RELAX_USE_32BIT (fragP) || !is_convertible (fragP))
	    {
	      size = 4;
	      md_number_to_chars (buf, comp_insn, 4);
	      exp_cond.X_op = O_symbol;
	      exp_cond.X_add_symbol = symbol_temp_new (sec, 0, fragP->fr_next);
	      exp_cond.X_add_number = 0;
	      fix_new_exp (fragP, where, 4, &exp_cond, 0,
			   BFD_RELOC_NDS32_15_PCREL);
	    }
	  else
	    {
	      size = 2;
	      md_number_to_chars (buf, comp_insn16, 2);
	      exp_cond.X_op = O_symbol;
	      exp_cond.X_add_symbol = symbol_temp_new (sec, 0, fragP->fr_next);
	      exp_cond.X_add_number = 0;
	      fixP = fix_new_exp (fragP, where, 2, &exp_cond, 0,
			     BFD_RELOC_NDS32_9_PCREL);
	      fixP->fx_no_overflow = 1;
	    }

	  /* Create sethi.  */
	  insn = INSN_SETHI_TA;
	  md_number_to_chars (buf + size, insn, 4);
	  fixP = fix_new_exp (fragP, where + size, 4, &exp, 0,
			 BFD_RELOC_NDS32_HI20);
	  fixP->fx_addnumber = fixP->fx_offset;
	  size += 4;

	  /* Create ori.  */
	  insn = INSN_ORI_TA;
	  md_number_to_chars (buf + size, insn, 4);
	  if (enable_relax_relocs)
	    fixP = fix_new_exp (fragP, where + size, 4, &exp, 0,
			   BFD_RELOC_NDS32_LO12S0_ORI);
	  else
	    fixP = fix_new_exp (fragP, where + size, 4, &exp, 0,
			   BFD_RELOC_NDS32_LO12S0);
	  fixP->fx_addnumber = fixP->fx_offset;
	  size += 4;

	  if (RELAX_USE_32BIT (fragP)
	      || (!is_convertible (fragP) && optimize))
	    {
	      /* 16-bit off or optimize for speed and first instruction is not
		 convertible; use jral.  */
	      insn = INSN_JR_TA;
	      md_number_to_chars (buf + size, insn, 4);
	      if (!RELAX_USE_32BIT (fragP) && optimize && enable_relax_relocs)
		{
		  /* 16-bit instruction fixup, so we can expand it to align
		     next label if necessary.  If this instruction is
		     expanded in linker the offset must be incremented by 1.  */
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = 0;
		  fix_new_exp (fragP, where + size, 4, &exp_relax, 0,
			       BFD_RELOC_NDS32_INSN16);

		  /* An invisible label relocation should have been created in
		     calc_branch_seq_size.  */
		}
	      size += 4;
	    }
	  else
	    {
	      /* use jr5  */
	      insn16 = INSN_JR5_TA;
	      md_number_to_chars (buf + size, insn16, 2);
	      size += 2;
	    }

	  if (!(insn_num == NDS32_INSN_BEQC || insn_num == NDS32_INSN_BNEC))
	    {
	      if (enable_relax_relocs)
		{
		  /* Create a relocation for this sequence, so linker can contract
		     it to smaller size.  */
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = SET_ADDEND (size, is_convertible (fragP),
				optimize, !RELAX_USE_32BIT (fragP));
		  fix_new_exp (fragP, where, size, &exp_relax, 0,
			       BFD_RELOC_NDS32_LONGJUMP3);
		}

	      /* Create label fixup for next frag
		 What's the size of 1st instruction in next frag?
		 The previous 16-bit instruction is 2 instructions above.  */
	      if (optimize && enable_relax_relocs)
		{
		  exp_relax.X_op = O_symbol;
		  exp_relax.X_add_symbol = abs_section_sym;
		  exp_relax.X_add_number = 2;
		  fix_new_exp (fragP->fr_next, 0,
			       0, &exp_relax, 0, BFD_RELOC_NDS32_LABEL);
		}
	    }
	  break;
	}
    }
  else if (RELAX_RELAXABLE (fragP))
    {
      org_size = 2;
      if (RELAX_RELAXED (fragP))
	{
	  /* Convert from 16-bit to 32.  Since this instruction is 32-bit,
	     do not remove LABEL relocation if exists.  */
	  if (!convert_16_to_32 (fragP, &insn))
	    as_fatal ("Unable to convert instruction 0x%04x from 16-bit to 32-bit",
	       (unsigned int) bfd_getb16 (fragP->fr_literal + fragP->fr_fix - 2));

	  size = 4;
	  md_number_to_chars (buf, insn, 4);
	  if (!RELAX_USE_32BIT (fragP) && optimize && enable_relax_relocs)
	    {
	      /* 16-bit instruction fixup, so we can contract it to align next
		 label if necessary.  if this instruction is expanded in linker
		 the offset must be incremented by 1.  */
	      exp_relax.X_op = O_symbol;
	      exp_relax.X_add_symbol = abs_section_sym;
	      exp_relax.X_add_number = 0;
	      fix_new_exp (fragP, where, 4, &exp_relax, 0,
			   BFD_RELOC_NDS32_INSN16);
	    }
	}
      else
	{
	  size = 2;
	}
    }
  else
    size = org_size;

  fragP->fr_fix += size - org_size;

  target_big_endian = saved_endian;

}

/* MD_PCREL_FROM_SECTION  */

long
nds32_pcrel_from_section (fixS *fixP, segT sec)
{
  if (fixP->fx_addsy != (symbolS *) NULL
      && (!S_IS_DEFINED (fixP->fx_addsy)
	  || S_GET_SEGMENT (fixP->fx_addsy) != sec
	  || S_IS_EXTERNAL (fixP->fx_addsy) || S_IS_WEAK (fixP->fx_addsy)))
    {
      if (S_GET_SEGMENT (fixP->fx_addsy) != sec
	  && S_IS_DEFINED (fixP->fx_addsy)
	  && !S_IS_EXTERNAL (fixP->fx_addsy) && !S_IS_WEAK (fixP->fx_addsy))
	return fixP->fx_offset;

      /* The symbol is undefined (or is defined but not in this section).
	 Let the linker figure it out.  */
      return 0;
    }

  return (fixP->fx_frag->fr_address + fixP->fx_where) & -2L;
}

/* This function returns the bfd reloc type for OPERAND of INSN at fixup FIXP.
   It returns BFD_RELOC_NONE if no reloc type can be found.  *FIXP may be
   modified if desired.  */

bfd_reloc_code_real_type
md_cgen_lookup_reloc (const CGEN_INSN *insn,
		      const CGEN_OPERAND *operand, fixS *fixP)
{
  switch (operand->type)
    {
    case NDS32_OPERAND_DISP16:
      return BFD_RELOC_NDS32_17_PCREL;
    case NDS32_OPERAND_DISP24:
      return BFD_RELOC_NDS32_25_PCREL;
    case NDS32_OPERAND_DISP14:
      return BFD_RELOC_NDS32_15_PCREL;
    case NDS32_OPERAND_DISP8:
      if (CGEN_INSN_BITSIZE (insn) == 32)
	return BFD_RELOC_NDS32_WORD_9_PCREL;
      else
	return BFD_RELOC_NDS32_9_PCREL;
    case NDS32_OPERAND_UHI20:
    case NDS32_OPERAND_ULO15D:
    case NDS32_OPERAND_ULO15W:
    case NDS32_OPERAND_ULO15H:
    case NDS32_OPERAND_ULO15B:
    case NDS32_OPERAND_ULO15:
    case NDS32_OPERAND_SLO15D:
    case NDS32_OPERAND_SLO15W:
    case NDS32_OPERAND_SLO15H:
    case NDS32_OPERAND_SLO15B:
    case NDS32_OPERAND_SLO15:
    case NDS32_OPERAND_SLO12W:
    case NDS32_OPERAND_SLO12D:
    case NDS32_OPERAND_SLO17W:
    case NDS32_OPERAND_SLO18H:
    case NDS32_OPERAND_SLO19:
      /* If low/high/shigh/sda was used, it is recorded in `opinfo'.  */
      if (fixP->fx_cgen.opinfo != 0)
	return fixP->fx_cgen.opinfo;
      break;
    default:
      /* Avoid -Wall warning.  */
      break;
    }

  return BFD_RELOC_NONE;
}

/* This function records a HI20 reloc for later matching with its LO12 cousin.  */

static void
nds32_record_hi20 (int reloc_type, fixS *fixP, segT seg ATTRIBUTE_UNUSED)
{
  struct nds32_hi_fixup *hi_fixup;

  gas_assert (reloc_type == BFD_RELOC_NDS32_HI20);

  hi_fixup = ((struct nds32_hi_fixup *)
	      xmalloc (sizeof (struct nds32_hi_fixup)));
  hi_fixup->fixp = fixP;
  hi_fixup->seg = now_seg;
  hi_fixup->next = nds32_hi_fixup_list;

  nds32_hi_fixup_list = hi_fixup;
}

#define GOT_NAME "_GLOBAL_OFFSET_TABLE_"
symbolS *GOT_symbol;

/* This function checks PIC attribute.  */

static inline int
nds32_PIC_related_p (symbolS *sym)
{
  expressionS *exp;

  if (!sym)
    return 0;

  if (sym == GOT_symbol)
    return 1;

  exp = symbol_get_value_expression (sym);

  return (exp->X_op == O_PIC_reloc
	  || exp->X_md == BFD_RELOC_NDS32_25_PLTREL
	  || exp->X_md == BFD_RELOC_NDS32_PLTREL_HI20
	  || exp->X_md == BFD_RELOC_NDS32_PLTREL_LO12
	  || exp->X_md == BFD_RELOC_NDS32_PLT_GOTREL_HI20
	  || exp->X_md == BFD_RELOC_NDS32_PLT_GOTREL_LO12
	  || nds32_PIC_related_p (exp->X_add_symbol)
	  || nds32_PIC_related_p (exp->X_op_symbol));
}

/* This function checks the fixup.  */

static inline int
nds32_check_fixup (expressionS *main_exp,
		   bfd_reloc_code_real_type *r_type_p)
{
  expressionS *exp = main_exp;

  if (exp->X_op == O_add && nds32_PIC_related_p (exp->X_op_symbol))
    return 1;

  if (exp->X_op == O_symbol && exp->X_add_symbol)
    {
      if (exp->X_add_symbol == GOT_symbol)
	{
	  *r_type_p = BFD_RELOC_NDS32_GOTPC20;
	  return 0;
	}
    }
  else if (exp->X_op == O_add)
    {
      exp = symbol_get_value_expression (exp->X_add_symbol);
      if (!exp)
	return 0;
    }

  if (exp->X_op == O_PIC_reloc || exp->X_md != BFD_RELOC_UNUSED)
    {
      *r_type_p = exp->X_md;
      if (exp == main_exp)
	exp->X_op = O_symbol;
      else
	{
	  main_exp->X_add_symbol = exp->X_add_symbol;
	  main_exp->X_add_number += exp->X_add_number;
	}
    }
  else
    return (nds32_PIC_related_p (exp->X_add_symbol)
	    || nds32_PIC_related_p (exp->X_op_symbol));

  return 0;
}

/* md_cgen_record_fixup_exp  */

fixS *
nds32_cgen_record_fixup_exp (fragS *frag,
			     int where,
			     const CGEN_INSN *insn,
			     int length,
			     const CGEN_OPERAND *operand,
			     int opinfo, expressionS *exp)
{
  fixS *fixP;
  bfd_reloc_code_real_type r_type = BFD_RELOC_UNUSED;

  if (nds32_check_fixup (exp, &r_type))
    as_bad (_("Invalid PIC expression."));

  fixP = gas_cgen_record_fixup_exp (frag, where, insn, length,
				    operand, opinfo, exp);

  switch (operand->type)
    {
    case NDS32_OPERAND_UHI20:
      /* If low/high/shigh/sda was used, it is recorded in `opinfo'.  */
      if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_HI20)
	nds32_record_hi20 (fixP->fx_cgen.opinfo, fixP, now_seg);
      break;
    case NDS32_OPERAND_SLO17W:
      /* jasonwu:
	   In order to make fp-as-gp work, two relocations are required:
	     1. BFD_RELOC_NDS32_SDA17S2
	     2. BFD_RELOC_NDS32_INSN16
	   For lwi.gp/swi.gp cases, BFD_RELOC_NDS32_SDA17S2 already exists.
	   We just need to create BFD_RELOC_NDS32_INSN16 relocation field
	   so that the link time optimization may have chance to do fp-as-gp.  */
      if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_SDA17S2)
	fix_new_exp (frag, where, 4, exp, 0, BFD_RELOC_NDS32_INSN16);
      break;
    default:
      /* Avoid -Wall warning.  */
      break;
    }

  switch (r_type)
    {
    default:
    case BFD_RELOC_UNUSED:
      return fixP;
    case BFD_RELOC_NDS32_GOTPC20:
      if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_HI20)
	r_type = BFD_RELOC_NDS32_GOTPC_HI20;
      else if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_LO12S0)
	r_type = BFD_RELOC_NDS32_GOTPC_LO12;
      break;
    case BFD_RELOC_NDS32_GOT20:
      if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_HI20)
	r_type = BFD_RELOC_NDS32_GOT_HI20;
      else if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_LO12S0)
	r_type = BFD_RELOC_NDS32_GOT_LO12;
      break;
    case BFD_RELOC_NDS32_GOTOFF:
      if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_HI20)
	r_type = BFD_RELOC_NDS32_GOTOFF_HI20;
      else if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_LO12S0)
	r_type = BFD_RELOC_NDS32_GOTOFF_LO12;
      break;
    case BFD_RELOC_NDS32_25_PLTREL:
      if (!pic_code)
	{
	  as_bad (_("Invalid PIC expression."));
	}
      else
	{
	  if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_HI20)
	    r_type = BFD_RELOC_NDS32_PLT_GOTREL_HI20;
	  else if (fixP->fx_cgen.opinfo == BFD_RELOC_NDS32_LO12S0)
	    r_type = BFD_RELOC_NDS32_PLT_GOTREL_LO12;
	}

      break;
    }

  fixP->fx_r_type = r_type;

  return fixP;
}

/* Return BFD reloc type from opinfo field in a fixS.
   It's tricky using fx_r_type in nds32_frob_file_before_fix because the values
   are BFD_RELOC_UNUSED + operand number.  */

#define FX_OPINFO_R_TYPE(f) ((f)->fx_cgen.opinfo)

/* tc_frob_file_before_fix  */

void
nds32_frob_file_before_fix (void)
{
  struct nds32_hi_fixup *l;

  for (l = nds32_hi_fixup_list; l != NULL; l = l->next)
    {
      segment_info_type *seginfo;
      int pass;

      gas_assert (FX_OPINFO_R_TYPE (l->fixp) == BFD_RELOC_NDS32_HI20);

      /* Check quickly whether the next fixup happens to be a matching low.  */
      if (l->fixp->fx_next != NULL
	  && (FX_OPINFO_R_TYPE (l->fixp->fx_next) == BFD_RELOC_NDS32_LO12S3
	      || FX_OPINFO_R_TYPE (l->fixp->fx_next) == BFD_RELOC_NDS32_LO12S2
	      || FX_OPINFO_R_TYPE (l->fixp->fx_next) == BFD_RELOC_NDS32_LO12S2_DP
	      || FX_OPINFO_R_TYPE (l->fixp->fx_next) == BFD_RELOC_NDS32_LO12S2_SP
	      || FX_OPINFO_R_TYPE (l->fixp->fx_next) == BFD_RELOC_NDS32_LO12S1
	      || FX_OPINFO_R_TYPE (l->fixp->fx_next) == BFD_RELOC_NDS32_LO12S0
	      || FX_OPINFO_R_TYPE (l->fixp->fx_next) == BFD_RELOC_NDS32_LO12S0_ORI)
	  && l->fixp->fx_addsy == l->fixp->fx_next->fx_addsy
	  && l->fixp->fx_offset == l->fixp->fx_next->fx_offset)
	continue;

      /* Look through the fixups for this segment for a matching `low'.
	 When we find one, move the high/shigh just in front of it.  We do
	 this in two passes.  In the first pass, we try to find a
	 unique `low'.  In the second pass, we permit multiple high's
	 relocs for a single `low'.  */
      seginfo = seg_info (l->seg);
      for (pass = 0; pass < 2; pass++)
	{
	  fixS *f;
	  fixS *prev = NULL;

	  for (f = seginfo->fix_root; f != NULL; f = f->fx_next)
	    {
	      /* Check whether this is a `low' fixup which matches l->fixp.  */
	      if ((FX_OPINFO_R_TYPE (f) == BFD_RELOC_NDS32_LO12S3
		   || FX_OPINFO_R_TYPE (f) == BFD_RELOC_NDS32_LO12S2
		   || FX_OPINFO_R_TYPE (f) == BFD_RELOC_NDS32_LO12S1
		   || FX_OPINFO_R_TYPE (f) == BFD_RELOC_NDS32_LO12S0
		   || FX_OPINFO_R_TYPE (f) == BFD_RELOC_NDS32_LO12S0_ORI)
		  && f->fx_addsy == l->fixp->fx_addsy
		  && f->fx_offset == l->fixp->fx_offset
		  && (pass == 1
		      || prev == NULL
		      || (FX_OPINFO_R_TYPE (prev) != BFD_RELOC_NDS32_HI20)
		      || prev->fx_addsy != f->fx_addsy
		      || prev->fx_offset != f->fx_offset))
		{
		  fixS **pf;

		  /* Move l->fixp before f.  */
		  for (pf = &seginfo->fix_root; *pf != l->fixp; pf = &(*pf)->fx_next)
		    gas_assert (*pf != NULL);

		  *pf = l->fixp->fx_next;

		  l->fixp->fx_next = f;
		  if (prev == NULL)
		    seginfo->fix_root = l->fixp;
		  else
		    prev->fx_next = l->fixp;

		  break;
		}

	      prev = f;
	    }

	  if (f != NULL)
	    break;

	  if (pass == 1 && warn_unmatched_high)
	    as_warn_where (l->fixp->fx_file, l->fixp->fx_line,
			   _("Unmatched high/shigh reloc"));
	}
    }
}

static bfd_boolean
nds32_relaxable_section (asection *sec)
{
  return ((sec->flags & SEC_DEBUGGING) == 0
	  && strcmp (sec->name, ".eh_frame") != 0);
}

/* TC_FORCE_RELOCATION  */

int
nds32_force_relocation (fixS *fix)
{
  switch (fix->fx_r_type)
    {
    case BFD_RELOC_NDS32_INSN16:
    case BFD_RELOC_NDS32_LABEL:
    case BFD_RELOC_NDS32_LONGCALL1:
    case BFD_RELOC_NDS32_LONGCALL2:
    case BFD_RELOC_NDS32_LONGCALL3:
    case BFD_RELOC_NDS32_LONGJUMP1:
    case BFD_RELOC_NDS32_LONGJUMP2:
    case BFD_RELOC_NDS32_LONGJUMP3:
    case BFD_RELOC_NDS32_LOADSTORE:
    case BFD_RELOC_NDS32_9_FIXED:
    case BFD_RELOC_NDS32_15_FIXED:
    case BFD_RELOC_NDS32_17_FIXED:
    case BFD_RELOC_NDS32_25_FIXED:
    case BFD_RELOC_NDS32_9_PCREL:
    case BFD_RELOC_NDS32_15_PCREL:
    case BFD_RELOC_NDS32_17_PCREL:
    case BFD_RELOC_NDS32_WORD_9_PCREL:
    case BFD_RELOC_NDS32_10_UPCREL:
    case BFD_RELOC_NDS32_25_PCREL:
    case BFD_RELOC_NDS32_MINUEND:
    case BFD_RELOC_NDS32_SUBTRAHEND:
      return 1;

    case BFD_RELOC_8:
    case BFD_RELOC_16:
    case BFD_RELOC_32:
    case BFD_RELOC_NDS32_DIFF_ULEB128:
      /* Linker should handle difference between two symbol.  */
      return fix->fx_subsy != NULL
	&& nds32_relaxable_section (S_GET_SEGMENT (fix->fx_addsy));
    case BFD_RELOC_64:
      if (fix->fx_subsy)
	as_bad ("Double word for difference between two symbols "
		"is not supported across relaxation.");
    default:
      ;
    }

  if (generic_force_reloc (fix))
    return 1;

  return fix->fx_pcrel;
}


/* TC_VALIDATE_FIX_SUB  */

int
nds32_validate_fix_sub (fixS *fix, segT add_symbol_segment)
{
  segT sub_symbol_segment;

  /* COLE: This code is referred from Xtensa.
     Check their implementation for details.  */

  /* Make sure both symbols are in the same segment, and that segment is
     "normal" and relaxable.  */
  sub_symbol_segment = S_GET_SEGMENT (fix->fx_subsy);
  return (sub_symbol_segment == add_symbol_segment
	  && add_symbol_segment != undefined_section);
}

void
md_number_to_chars (char *buf, valueT val, int n)
{
  if (target_big_endian)
    number_to_chars_bigendian (buf, val, n);
  else
    number_to_chars_littleendian (buf, val, n);
}

/* Equal to MAX_PRECISION in atof-ieee.c.  */
#define MAX_LITTLENUMS 6

/* This function is called to convert an ASCII string into a floating point
   value in format used by the CPU.  */

char *
md_atof (int type, char *litP, int *sizeP)
{
  int i;
  int prec;
  LITTLENUM_TYPE words[MAX_LITTLENUMS];
  char *t;

  switch (type)
    {
    case 'f':
    case 'F':
    case 's':
    case 'S':
      prec = 2;
      break;
    case 'd':
    case 'D':
    case 'r':
    case 'R':
      prec = 4;
      break;
    default:
      *sizeP = 0;
      return _("Bad call to md_atof()");
    }

  t = atof_ieee (input_line_pointer, type, words);
  if (t)
    input_line_pointer = t;
  *sizeP = prec * sizeof (LITTLENUM_TYPE);

  if (target_big_endian)
    {
      for (i = 0; i < prec; i++)
	{
	  md_number_to_chars (litP, (valueT) words[i],
			      sizeof (LITTLENUM_TYPE));
	  litP += sizeof (LITTLENUM_TYPE);
	}
    }
  else
    {
      for (i = prec - 1; i >= 0; i--)
	{
	  md_number_to_chars (litP, (valueT) words[i],
			      sizeof (LITTLENUM_TYPE));
	  litP += sizeof (LITTLENUM_TYPE);
	}
    }

  return 0;
}


/* Relaxation zone begin.  */

#define NDS32_GOT_MASK  1
#define NDS32_GOTOFF_MASK 2
#define NDS32_PLT_GOT_MASK 3
#define NDS32_MULCALL_MASK 4

extern int size_inc_line_addr (int, addressT);

static int analysis_rec_bb (nds32_insn_instant *, basic_block *, int, int);
static int analysis_rec (nds32_insn_instant *, basic_block *, int, int);
static int life_time_analysis_ls_succ (nds32_insn_instant *);
void nds32_set_section_relocs (asection *, arelent **, unsigned int);

static int ld_st_address_len_type;
static int current_reloc_type_mask;
static symbolS *current_trace_sym;
static valueT current_trace_addend;
static int prev_insn_num;

static int
get_sym_addend_from_insn (nds32_insn_instant *insn_p, symbolS ** sym,
			  valueT *addend)
{
  int i;

  if (insn_p->md_relax)
    {
      /* fixups[i] not exists && md_relax
	 For those instructions with machine specific relaxations,
	 we can only get the target through the info stored in the frag.  */
      if (S_GET_SEGMENT (insn_p->frag->fr_symbol) == expr_section)
	{
	  *sym = NULL;
	  *addend = 0;
	}
      else
	{
	  *sym = insn_p->frag->fr_symbol;
	  *addend = insn_p->frag->fr_offset;
	}
      i = insn_p->num_fixups;
    }
  else
    {
      for (i = 0; i < insn_p->num_fixups; i++)
	if (insn_p->fixups[i]->fx_addsy != NULL)
	  break;

      /* The basic method to get branch target is get them from fixups.  */
      if (i != insn_p->num_fixups && insn_p->fixups[i]->fx_subsy == NULL)
	{
	  *sym = insn_p->fixups[i]->fx_addsy;
	  *addend = insn_p->fixups[i]->fx_offset;
	}
      else
	{
	  *sym = NULL;
	  *addend = 0;
	}
    }
  return i;
}

static void
check_label_belong_to_wrong_bb (void)
{
  basic_block *bb;
  insn_label_list *sym_list;

  bb = bb_list;
  while (bb)
    {
      sym_list = bb->label_list;
      while (sym_list)
	{
	  if (bb->now_seg != S_GET_SEGMENT (sym_list->label))
	    as_warn (_("[gas warning] Basic block contains a label"
		       "seats in different section, file: %s, line:%d"),
		     bb->filename, bb->line_num);
	  sym_list = sym_list->next;
	}
      bb = bb->list_next;
    }
}

static void
count_bb_known_pred (void)
{
  basic_block *bb;
  int func_mask;

  bb = bb_list;

  while (bb != NULL)
    {
      if (bb->cfg_target)
	bb->cfg_target->known_pred++;
      if (bb->cfg_next)
	bb->cfg_next->known_pred++;
      else
	{
	  if (bb->insn_tail)
	    {
	      basic_block *ifc_bb;
	      func_mask = is_func_branch (bb->insn_tail->insn_num);

	      switch (func_mask)
		{
		case IS_FUNC_CALL_MASK:
		  bb->list_next->known_pred++;
		  break;
		case IS_COND_FUNC_CALL_MASK:
		  ifc_bb = bb->cfg_target;

		  while (ifc_bb && ifc_bb->insn_tail)
		    {
		      /* If J is reached, then list_next is unreachable.  */
		      func_mask = is_func_branch (ifc_bb->insn_tail->insn_num);
		      ifc_bb->in_common++;
		      switch (func_mask)
			{
			case IS_COND_FUNC_CALL_MASK:
			  as_warn (_("Assembler cannot handle nested IFCALL."));
			case IS_COND_FUNC_RETURN_MASK:
			case IS_FUNC_CALL_MASK:
			  bb->list_next->known_pred++;
			  goto out_ifret_scanning;
			default:
			  if (is_conditional_branch_instruction (ifc_bb->insn_tail->insn_num)
			      || is_direct_branch_instruction (ifc_bb->insn_tail->insn_num))
			    goto out_ifret_scanning;
			  break;
			}
		      ifc_bb = ifc_bb->list_next;
		    }
out_ifret_scanning:
		  break;
		}
	    }
	}

      bb = bb->list_next;
    }
}

static void
establish_label_hash (void)
{
  basic_block *bb;
  insn_label_list *sym_list;
  asymbol *bfdsym_t;
  bfdsym_bb_map *bfdsym_bb_map_t, *bfdsym_bb_map_t2;

  bb = bb_list;

  while (bb != NULL)
    {
      sym_list = bb->label_list;
      while (sym_list != NULL)
	{
	  bfdsym_t = symbol_get_bfdsym (sym_list->label);
	  bfdsym_bb_map_t = (bfdsym_bb_map *) hash_find (bfdsym_hash, bfdsym_t->name);
	  if (!bfdsym_bb_map_t)
	    {
	      bfdsym_bb_map_t = new_bfdsym_bb_map (bb, bfdsym_t, NULL);
	      hash_insert (bfdsym_hash, bfdsym_t->name, bfdsym_bb_map_t);
	    }
	  else
	    {
	      if ((bfdsym_bb_map_t2 = find_bfdsym_bb_map (bfdsym_bb_map_t, bfdsym_t)))
		{
		  if (bb != bfdsym_bb_map_t2->bb)
		    as_warn (_("[gas warning] Different basic blocks defined "
			       "the same bfd symbol"));
		}
	      else
		{
		  bfdsym_bb_map_t = new_bfdsym_bb_map (bb, bfdsym_t, bfdsym_bb_map_t);
		  hash_replace (bfdsym_hash, bfdsym_t->name, bfdsym_bb_map_t);
		}
	    }
	  sym_list = sym_list->next;
	}
      bb = bb->list_next;
    }
}

static void
build_cfg (void)
{
  basic_block *bb, *bb2, *bb_next;
  int br_type;
  valueT addend;
  nds32_insn_instant *insn_s;
  symbolS *sym;
  bfdsym_bb_map *bfdsym_bb_map_t;

  bb = bb_list;

  check_label_belong_to_wrong_bb ();
  establish_label_hash ();

  while (bb != NULL)
    {
      insn_s = bb->insn_tail;
      if (insn_s == NULL)
	{
	  bb = bb->list_next;
	  continue;
	}

      /* Get the closest next basic block in the same section.  */
      bb2 = bb->list_next;
      while (bb2 != NULL && bb2->now_seg != bb->now_seg)
	bb2 = bb2->list_next;
      bb_next = bb2;

      br_type = is_direct_branch_instruction (insn_s->insn_num);
      switch (br_type)
	{
	case INDIRECT_BRANCH_MASK:
	  br_type = is_conditional_branch_instruction (insn_s->insn_num);
	  if (br_type == CONDITIONAL_BRANCH_MASK)
	    bb->cfg_next = bb_next;
	  else
	    bb->cfg_next = NULL;
	  bb->cfg_target = bb_indirect;
	  break;
	case DIRECT_BRANCH_MASK:
	  br_type = is_conditional_branch_instruction (insn_s->insn_num);
	  if (br_type == CONDITIONAL_BRANCH_MASK)
	    bb->cfg_next = bb_next;
	  else
	    bb->cfg_next = NULL;

	  /* Check if there were non-null subsy.  */

	  get_sym_addend_from_insn (insn_s, &sym, &addend);
	  if (sym == NULL)
	    {
	      bb->cfg_target = bb_indirect;
	      break;
	    }

	  if ((bfdsym_bb_map_t = (bfdsym_bb_map *) hash_find (bfdsym_hash,
					    symbol_get_bfdsym (sym)->name)))
	    {
	      if ((bfdsym_bb_map_t = find_bfdsym_bb_map (bfdsym_bb_map_t,
				       symbol_get_bfdsym (sym))))
		{
		  bb->cfg_target = bfdsym_bb_map_t->bb;
		}
	    }

	  /* A function call to external function
	     is considered as indirect branch.  */
	  if (bb->cfg_target == NULL)
	    bb->cfg_target = bb_indirect;
	  break;
	default:
	  bb->cfg_next = bb_next;
	}
      bb = bb->list_next;
    }
}

/* Build def-use information in terms of a single basic block.  */

static void
def_use_analysis (void)
{
  basic_block *bb = bb_list;
  nds32_insn_instant *insn;
  dep_node *dep;
  nds32_insn_instant *set_gr[32];
  nds32_insn_instant *use_gr[32];

  while (bb != NULL)
    {
      memset (set_gr, 0, 32 * sizeof (nds32_insn_instant *));
      memset (use_gr, 0, 32 * sizeof (nds32_insn_instant *));
      insn = bb->insn_head;
      while (insn != NULL && insn != bb->insn_tail->next)
	{
	  dep = insn->gr_dep_list;
	  while (dep != NULL)
	    {
	      if (dep->flag & (short) CGEN_OPINST_INPUT_MASK)
		{
		  use_gr[dep->reg_num] = insn;
		  if (set_gr[dep->reg_num] == NULL
		      && bb->use_before_set_gr[dep->reg_num] == NULL)
		    bb->use_before_set_gr[dep->reg_num] = insn;
		}
	      dep = dep->next;
	    }

	  /* FIXME: Please review set_before_use.
	       case 1		  case 2
	       addi $r3, $r4, 0   addi $r4, $r3, 0
	       addi $r4, $r3, 0   addi $r3, $r4, 0
	     Both cases are not set_before_use,
	     so I think either the name is misleading,
	     or this is a bug.  */

	  dep = insn->gr_dep_list;
	  while (dep != NULL)
	    {
	      if (dep->flag & (short) CGEN_OPINST_OUTPUT_MASK)
		{
		  set_gr[dep->reg_num] = insn;
		  if (use_gr[dep->reg_num] == NULL
		      && bb->set_before_use_gr[dep->reg_num] == NULL)
		    bb->set_before_use_gr[dep->reg_num] = insn;
		}
	      dep = dep->next;
	    }
	  insn = insn->next;
	}
      bb = bb->list_next;
    }
}

static int
check_insn_output_reg_valid (dep_node *node_p)
{
  int regT = -1;
  while (node_p != NULL)
    {
      if (node_p->flag & (short) CGEN_OPINST_OUTPUT_MASK)
	{
	  regT = node_p->reg_num;
	  break;
	}
      node_p = node_p->next;
    }
  if (regT < 0 || regT > 31)
    {
      as_bad ("CFG : invalid register number $rt of sethi\n");
      abort ();
    }
  return regT;
}

/* This function is used to check if a register is used or defined by a instruction.
   It can only check one flag at a time.  */

static bfd_boolean
find_reg_in_insn (dep_node *node_p, short reg_t, short flag_t)
{
  dep_node *node_t = node_p;

  while (node_t != NULL)
    {
      if (node_t->reg_num == reg_t && (node_t->flag |= flag_t > 0))
	return TRUE;
      node_t = node_t->next;
    }
  return FALSE;
}

static void
insert_relax_type (nds32_insn_instant *insn_p, int reloc_type, int data_size,
		   int arg, expressionS *exp_p)
{
  expressionS exp;
  fragS *fragP;
  fixS *fixP;
  int where;

  frchain_now = insn_p->parent->frchain_now;
  fragP = insn_p->frag;
  where = (insn_p->addr - insn_p->frag->fr_literal) / OCTETS_PER_BYTE;

  /* Place a relocation data here.  */
  exp.X_op = O_symbol;
  exp.X_add_symbol = abs_section_sym;
  exp.X_add_number = 0;


  switch (reloc_type)
    {
    case BFD_RELOC_NDS32_LOADSTORE:
      exp.X_add_number = SET_ADDEND (4, is_convertible (insn_p->frag),
		    optimize, !RELAX_USE_32BIT (fragP));
      exp.X_add_number |= ((arg & 0x3f) << 8);
      fixP = fix_new_exp (insn_p->frag, where, data_size, &exp, 0, reloc_type);
      break;
    case BFD_RELOC_NDS32_RELAX_ENTRY:
    case BFD_RELOC_NDS32_PTR_COUNT:
      exp.X_add_number = arg;
      fixP = fix_new_exp (insn_p->frag, where, 0, &exp, 0, reloc_type);
      fixP->fx_no_overflow = 1;
      break;
    case BFD_RELOC_NDS32_PTR:
      fixP = fix_new_exp (insn_p->frag, where, 0, exp_p, 0, reloc_type);
      fixP->fx_no_overflow = 1;
      break;
    case BFD_RELOC_NDS32_GOT_SUFF:
    case BFD_RELOC_NDS32_GOTOFF_SUFF:
    case BFD_RELOC_NDS32_PLT_GOT_SUFF:
      fixP = fix_new_exp (insn_p->frag, where, data_size, exp_p, 0, reloc_type);
      fixP->fx_no_overflow = 1;
      break;
    case BFD_RELOC_NDS32_MULCALL_SUFF:
      fixP = fix_new_exp (insn_p->frag, where, data_size, exp_p, 0, reloc_type);
      fixP->fx_no_overflow = 1;
      if (insn_p->insn_num == NDS32_INSN_ORI
	  || insn_p->insn_num == NDS32_INSN_MOV55)
	fixP->fx_addnumber = 1;
      break;
    default:
      if (!exp_p)
	fixP = fix_new_exp (insn_p->frag, where, data_size, &exp, 0, reloc_type);
      else
	fixP = fix_new_exp (insn_p->frag, where, data_size, exp_p, 0, reloc_type);
    }
}

/* Make a temp expression for a symbol before making it a fixup.  */

static void
insert_relax_type_sym (nds32_insn_instant *insn_p, int reloc_type,
		       int data_size, symbolS *symp, int addnumber)
{
  expressionS exp_t;

  exp_t.X_op = O_symbol;
  exp_t.X_add_symbol = symp;
  exp_t.X_add_number = addnumber;
  insert_relax_type (insn_p, reloc_type, data_size, 0, &exp_t);
}

/* Give instruction insn_p an NDS32_PTR reloc for each
   instruction stored in the list insn_list_p.  */

static void
insert_nds32_fix_reloc_node (reloc_tree_node *reloc_node_p,
			     reloc_tree_node *reloc_node_q, int reloc_type)
{
  symbolS *sym_t;
  nds32_insn_instant *insn_t = reloc_node_q->insn, *insn_root =
    reloc_node_p->insn;

  sym_t = symbol_temp_new (insn_t->parent->now_seg,
		     insn_t->addr - insn_t->frag->fr_literal, insn_t->frag);
  insert_relax_type_sym (insn_root, reloc_type, 4, sym_t, 0);
}

static void
ld_st_data_size (nds32_insn_instant *insn_p)
{
  switch (insn_p->insn_num)
    {
    case NDS32_INSN_LBI:
    case NDS32_INSN_SBI:
    case NDS32_INSN_LBSI:
    case NDS32_INSN_LB:
    case NDS32_INSN_LBS:
    case NDS32_INSN_SB:
      ld_st_address_len_type |= 0x01;
      break;
    case NDS32_INSN_LHI:
    case NDS32_INSN_SHI:
    case NDS32_INSN_LHSI:
    case NDS32_INSN_LH:
    case NDS32_INSN_LHS:
    case NDS32_INSN_SH:
      ld_st_address_len_type |= 0x02;
      break;
    case NDS32_INSN_LWI:
    case NDS32_INSN_SWI:
    case NDS32_INSN_LW:
    case NDS32_INSN_SW:
      ld_st_address_len_type |= 0x04;
      break;
    case NDS32_INSN_FLSI:
    case NDS32_INSN_FSSI:
      ld_st_address_len_type |= 0x08;
      break;
    case NDS32_INSN_FLDI:
    case NDS32_INSN_FSDI:
      ld_st_address_len_type |= 0x10;
      break;
    case NDS32_INSN_ORI:
      ld_st_address_len_type |= 0x20;
      break;
    default:
      /* Do nothing. (-Wswitch). */
      break;
    }
  return;
}

/* Control some relaxation based on USE-DEF pair.
   Return TRUE for reject.  */

static int
relax_barrier (nds32_insn_instant *insn_def, nds32_insn_instant *insn_use)
{
  /* This function acts as a barrier for DEF-USE across common blokc.
     In general, this is not allowed, because a USE in common block
     may have multiple reaching definition from precessors, and
     a DEF in common will be used for all its successors.

	D0  D1  D2
	 \  |  /
	   USE (common)		DEF (common)
	 /  |  \		  /  |  \
				 U0 U1  U2

     Besides, in C++, the edge to catch-block is invisible,
     so we should avoid relax la-bral to jal for correctness.
	 A
	 try:
	    B (throw)
	    goto out
	 catch:
	    C    <-- invisible edge from B to C
	 out:
	 D

     However, we keep the definition of insn_p (e.g., SETHI) in common block,
     ONLY if we cannot find an ORI to relax in the same common block.

     I handle it this way because linker always relax ORI-LO12 to ADDI.GP.
     If we keep both SETHI and ORI untouched, they becomes a strange code pattern.
     For example,

	     sethi  $r6, hi20(foo)       =>   sethi    $r6, hi20(foo)
	     ori    $r6, $r6, lo12(foo)       addi.gp  $r6, foo

     case 1 - Not found.  Keep SETHI

	.Lcommon:
	     sethi  $r6, hi20(foo)       =>   sethi  $r6, hi20(foo)
	     ifret			      ireft

     case 0 - Found ORI.  Relax it.

	.Lcommon:
	     sethi  $r6, hi20(foo)
	     ori    $r6, $r6, lo12(foo)  =>   addi.gp  $r6, foo
	     ifret			      ireft
     */

  static int is_cpp = -1;

  if (is_cpp == -1)
    is_cpp =  bfd_get_section_by_name (stdoutput, ".gcc_except_table") != NULL;

  switch (insn_def->insn_num)
    {
    case NDS32_INSN_SETHI:
      if (insn_use->insn_num == NDS32_INSN_ORI
	  && insn_use->parent->in_common)
	return 0;
    case NDS32_INSN_ORI:
      if (is_cpp && (insn_use->insn_num == NDS32_INSN_JRAL
	  || insn_use->insn_num == NDS32_INSN_JRAL5))
	return 1;
    case NDS32_INSN_JRAL:
    case NDS32_INSN_JRAL5:
    default:
      break;
    }

  if (insn_def->parent->in_common
      || insn_use->parent->in_common)
    return 1;

  return 0;
}

static int
trace_bb_def_use (nds32_insn_instant *insn_p, nds32_insn_instant *insn_r,
		  int regT)
{
  nds32_insn_instant *insn_s = insn_r;
  symbolS *sym, *tmp_sym;
  valueT addend, tmp_addend;
  short flag;
  dep_node *node, *node2;
  reloc_tree_node *reloc_list_t = NULL, *reloc_node_t;
  int pass_next = 0, node_cond = 0;

  /* Since sethi and ori both have relocation type,
     we should check if their targets are the same.
     Here we get the symbol and addend from relocation type of sethi.  */
  get_sym_addend_from_insn (insn_p, &sym, &addend);

  /* COLE: It seems `prev_insn_num' is used to track
     sethi-ori and sethi-ori-add patterns.  */

  while (insn_s != NULL && insn_s != insn_r->parent->insn_tail->next)
    {
      node = insn_s->gr_dep_list;
      pass_next = pass_next ? pass_next - 1 : pass_next;
      while (node != NULL)
	{
	  if (node->reg_num == ((short) 0xffff))
	    {
	      if (node->flag & (short) CGEN_OPINST_INPUT_MASK)
		return CGEN_OPINST_INPUT_MASK;
	      else if (node->flag & (short) CGEN_OPINST_OUTPUT_MASK)
		return CGEN_OPINST_OUTPUT_MASK;
	    }
	  switch (insn_p->insn_num)
	    {
	    case NDS32_INSN_SETHI:
	      if (node->reg_num == regT)
		{
		  flag = node->flag;
		  if (flag & (short) CGEN_OPINST_INPUT_MASK)
		    {
		      get_sym_addend_from_insn (insn_s, &tmp_sym, &tmp_addend);

		      if (is_lo12_mem_imm_instruction (insn_s->insn_num) > 0)
			{
			  /* For cases:
			       sethi   $rt, hi20(SYM)
			       lwi     $rd, $rt, lo12(SYM)
			     Only happened in non-PIC object.  */

			  if (tmp_sym == NULL
			      || symbol_get_bfdsym (tmp_sym) != symbol_get_bfdsym (sym)
			      || addend != tmp_addend)
			    return CGEN_OPINST_INPUT_MASK;
			  ld_st_data_size (insn_s);
			  insert_relax_type (insn_s, BFD_RELOC_NDS32_INSN16,
					     4, 0, NULL);
			}
		      else if (relax_barrier (insn_p, insn_s))
			return CGEN_OPINST_INPUT_MASK;
		      else if (insn_s->insn_num == NDS32_INSN_ORI)
			{
			  /* For cases:
			       sethi   $rt, hi20(SYM)
			       ori     $rd, $rt, lo12(SYM)
			     May happened in both PIC and non-PIC object.
			     For non-PIC object, we only handle sethi/ori pair.
			     For PIC object, we handle much complicate cases.  */
			  if (tmp_sym == NULL
			      || symbol_get_bfdsym (tmp_sym) != symbol_get_bfdsym (sym)
			      || addend != tmp_addend)
			    return CGEN_OPINST_INPUT_MASK;
			  ld_st_data_size (insn_s);

			  /* Backup needed data of current sethi instruction for further use.  */
			  insert_relax_type (insn_s, BFD_RELOC_NDS32_INSN16,
					     4, 0, NULL);
			  prev_insn_num = NDS32_INSN_SETHI;

			  /* Discover dependency of current ORI instruction and
			     followed instructions.  life_time_analysis_ori is
			     invoked recursively till the last instruction in
			     the code pattern.  */
			  if (current_reloc_type_mask == NDS32_PLT_GOT_MASK
			      || current_reloc_type_mask == 0)
			    reloc_list_t = reloc_list_now;
			  reloc_list_now = reloc_node_t = NULL;

			  if (life_time_analysis_ls_succ (insn_s)
			      && reloc_list_now)
			    {
			      reloc_node_t = new_reloc_node_sibling (NULL, insn_s);
			      if (current_reloc_type_mask != NDS32_PLT_GOT_MASK
				  && current_reloc_type_mask != 0)
				bind_reloc_list_insn (reloc_node_t);
			      bind_reloc_node_child_sibling (reloc_node_t,
							     reloc_list_now);
			      if (current_reloc_type_mask < 4
				  && current_reloc_type_mask > 0)
				reloc_node_t->type_mask = current_reloc_type_mask;
			      else if (current_reloc_type_mask == 0)
				reloc_node_t->type_mask = NDS32_MULCALL_MASK;
			      while (reloc_list_now)
				{
				  bind_reloc_list_insn (reloc_list_now);
				  reloc_list_now = reloc_list_now->sibling;
				}
			    }
			  else
			    free_reloc_node_sibling (&reloc_list_now);

			  if (current_reloc_type_mask == NDS32_PLT_GOT_MASK
			      || current_reloc_type_mask == 0)
			    {
			      if (!reloc_node_t)
				reloc_node_t = new_reloc_node_sibling (NULL, insn_s);
			      reloc_node_t->sibling = reloc_list_t;
			      reloc_list_now = reloc_node_t;
			    }
			  /* Restore backed-up data.  */
			  prev_insn_num = 0;
			}
		      else
			{
			  return CGEN_OPINST_INPUT_MASK;
			  /* It is used.  Set this sethi none relaxation.  */
			}
		    }

		  if (flag & (short) CGEN_OPINST_OUTPUT_MASK)
		    return CGEN_OPINST_OUTPUT_MASK;
		}
	      break;

	    case NDS32_INSN_ORI:
	      if (node->reg_num == regT)
		{
		  flag = node->flag;
		  if (flag & (short) CGEN_OPINST_INPUT_MASK)
		    {
		      if (prev_insn_num != NDS32_INSN_SETHI)
			return CGEN_OPINST_INPUT_MASK;
		      else if (relax_barrier (insn_p, insn_s))
			return CGEN_OPINST_INPUT_MASK;
		      else if (current_reloc_type_mask == NDS32_GOT_MASK)
			{
			  /* sethi    rt1, hi20(sym@GOT)
			     ori      rt2, rt1, lo12(sym@GOT)
			     lw       rd, [gp + rt2]  */
			  if (insn_s->insn_num == NDS32_INSN_LW)
			    {
			      /* If there were no gp encoded in this instruction,
				 this is not a gp-relative access.  Skip it.  */
			      if (find_reg_in_insn
				  (insn_s->gr_dep_list, (short) REG_GP,
				   (short) CGEN_OPINST_INPUT_MASK))
				{
				  reloc_list_now = new_reloc_node_sibling (reloc_list_now, insn_s);
				  bb_list_in_critical (nds32_path_bb_list);
				}
			      else
				return CGEN_OPINST_INPUT_MASK;
			    }
			  else
			    return CGEN_OPINST_INPUT_MASK;
			}
		      else if (current_reloc_type_mask == NDS32_GOTOFF_MASK)
			{
			  /* sethi    rt1, hi20(sym@GOTOFF)
			     ori      rt2, rt1, lo12(sym@GOTOFF)
			     lw       rd, [gp + rt2]  */
			  if (is_lo12_mem_reg_instruction (insn_s->insn_num) >
			      0 || insn_s->insn_num == NDS32_INSN_ADD
			      || insn_s->insn_num == NDS32_INSN_ADD45)
			    {
			      /* If there were no gp encoded in this instruction,
				 this is not a gp-relative access.  Skip it.  */
			      if (find_reg_in_insn
				  (insn_s->gr_dep_list, (short) REG_GP,
				   (short) CGEN_OPINST_INPUT_MASK))
				{
				  reloc_list_now = new_reloc_node_sibling (reloc_list_now, insn_s);
				  bb_list_in_critical (nds32_path_bb_list);
				}
			      else
				return CGEN_OPINST_INPUT_MASK;
			    }
			  else
			    return CGEN_OPINST_INPUT_MASK;
			}
		      else if (current_reloc_type_mask == NDS32_PLT_GOT_MASK)
			{
			  /* Not sethi if ori contains a relocation data.  */
			  if (insn_s->insn_num == NDS32_INSN_ADD
			      || insn_s->insn_num == NDS32_INSN_ADD45)
			    {
			      prev_insn_num = NDS32_INSN_ORI;

			      reloc_list_t = new_reloc_node_sibling (reloc_list_now, insn_s);
			      reloc_list_now = NULL;

			      if (life_time_analysis_ls_succ (insn_s))
				{
				  bind_reloc_node_child_sibling (reloc_list_t,
								 reloc_list_now);
				  while (reloc_list_now)
				    {
				      bind_reloc_list_insn (reloc_list_now);
				      reloc_list_now = reloc_list_now->sibling;
				    }
				}
			      else
				free_reloc_node_sibling (&reloc_list_now);
			      reloc_list_now = reloc_list_t;
			      bb_list_in_critical (nds32_path_bb_list);

			      prev_insn_num = NDS32_INSN_SETHI;
			    }
			  else if (insn_s->insn_num == NDS32_INSN_JRAL
				   || insn_s->insn_num == NDS32_INSN_JRAL5)
			    {
			      reloc_list_now = new_reloc_node_sibling (reloc_list_now, insn_s);
			      bb_list_in_critical (nds32_path_bb_list);
			    }
			  else
			    /* FIXME:  */
			    return CGEN_OPINST_INPUT_MASK;
			}
		      else
			{
			  if (insn_s->insn_num == NDS32_INSN_JRAL
			      || insn_s->insn_num == NDS32_INSN_JRAL5)
			    {
			      /* If there were no gp encoded in this instruction,
				 this is not a gp-relative access.  Skip it.  */
			      if (!pass_next)
				{
				  reloc_list_now = new_reloc_node_sibling (reloc_list_now, insn_s);
				  bb_list_in_critical (nds32_path_bb_list);
				}
			    }
			  /* Extra support for n1212hc case, is this really make sense since
			     the dynamic linked binary may need to update $ta.  */
			  else if ((insn_s->insn_num == NDS32_INSN_MOV55
				    || insn_s->insn_num == NDS32_INSN_ORI)
				   && insn_s->next
				   && (insn_s->next->insn_num == NDS32_INSN_JRAL
				       || insn_s->next->insn_num == NDS32_INSN_JRAL5))
			    {
			      node2 = insn_s->gr_dep_list;
			      node_cond = 0;
			      while (node2)
				{
				  if (node2->reg_num == regT
				      && (node2->flag & (short)
					  CGEN_OPINST_INPUT_MASK))
				    node_cond |= 1;
				  if (node2->reg_num == REG_R15
				      && (node2->flag & (short)
					  CGEN_OPINST_OUTPUT_MASK))
				    node_cond |= 2;
				  node2 = node2->next;
				}
			      node2 = insn_s->gr_dep_list;
			      while (node2)
				{
				  if (node2->reg_num == regT
				      && (node2->flag & (short)
					  CGEN_OPINST_INPUT_MASK))
				    break;
				}
			      if (node_cond == 3 && node2)
				{
				  reloc_list_now = new_reloc_node_sibling (reloc_list_now, insn_s);
				  bb_list_in_critical (nds32_path_bb_list);
				  /* A two instruction block.  */
				  pass_next = 2;
				}
			      else
				return CGEN_OPINST_INPUT_MASK;
			    }
			  else
			    return CGEN_OPINST_INPUT_MASK;
			}
		    }

		  if (flag & (short) CGEN_OPINST_OUTPUT_MASK)
		    return CGEN_OPINST_OUTPUT_MASK;
		}
	      break;

	    case NDS32_INSN_ADD:
	    case NDS32_INSN_ADD45:
	      if (node->reg_num == regT)
		{
		  flag = node->flag;
		  if (flag & CGEN_OPINST_INPUT_MASK)
		    {
		      if (prev_insn_num != NDS32_INSN_ORI)
			return CGEN_OPINST_INPUT_MASK;
		      else if (current_reloc_type_mask == NDS32_PLT_GOT_MASK
			       && (insn_s->insn_num == NDS32_INSN_JRAL
				   || insn_s->insn_num == NDS32_INSN_JRAL5))
			{
			  reloc_list_now = new_reloc_node_sibling (reloc_list_now, insn_s);
			  bb_list_in_critical (nds32_path_bb_list);
			}
		      else
			return CGEN_OPINST_INPUT_MASK;
		    }
		  if (flag & (short) CGEN_OPINST_OUTPUT_MASK)
		    return CGEN_OPINST_OUTPUT_MASK;
		}
	      break;

	    case NDS32_INSN_INVALID:
	      if (node->reg_num == regT)
		{
		  flag = node->flag;
		  if (flag & (short) CGEN_OPINST_INPUT_MASK)
		    return CGEN_OPINST_INPUT_MASK;
		  else if (flag & (short) CGEN_OPINST_OUTPUT_MASK)
		    return CGEN_OPINST_OUTPUT_MASK;
		}
	      break;
	    default:
	      break;
	    }
	  node = node->next;
	}
      insn_s = insn_s->next;
    }

  /* In general, if the DEF-instruction is in common block,
     it is used by all the possible successor, so we should
     keep it alive by assuming it it USED.
     See relax_barrier () for futher information.  */
  if (insn_p->parent->in_common)
    return CGEN_OPINST_INPUT_MASK;

  return 0;
}

static int
analysis_rec_bb (nds32_insn_instant *insn_p, basic_block *bb_p, int regT,
		 int level)
{
  int func_mask, used_by_succ = 0;

  func_mask = is_func_branch (bb_p->insn_tail->insn_num);
  if (func_mask == 0)
    {
      used_by_succ = analysis_rec (insn_p, bb_p->cfg_next, regT, level + 1);
      if (used_by_succ != CGEN_OPINST_INPUT_MASK)
	{
	  used_by_succ = analysis_rec (insn_p, bb_p->cfg_target, regT, level + 1);
	}
    }
  else if (func_mask == (int) IS_FUNC_RETURN_MASK)
    {
      /* Update of register[0~1] can't be suppressed when function return
	 since these registers are used as return value.  */
      if (regT > 1 && regT < 26)
	return 0;
      else
	return CGEN_OPINST_INPUT_MASK;
    }
  else if (func_mask == (int) IS_COND_FUNC_RETURN_MASK)
    {
      if (!is_conservative_ifc)
	{
	  if (ifc_mode == 1)
	    {
	      ifc_mode = 0;
	      return 0;
	    }
	  else
	    used_by_succ = analysis_rec (insn_p, bb_p->list_next, regT, level + 1);
	}
      else
	{
	  ifc_mode = 0;
	  return CGEN_OPINST_INPUT_MASK;
	}
    }
  else if (func_mask == (int) IS_COND_FUNC_CALL_MASK)
    {
      if (bb_p->insn_tail->insn_num == NDS32_INSN_IFCALL
	  || bb_p->insn_tail->insn_num == NDS32_INSN_IFCALL9)
	{
	  enum LEAVING_REASON { LRE_NONE, LRE_RET, LRE_NONRET } leaving_reason = LRE_NONE;
	  basic_block *ifc_bb;

	  ifc_mode = 1;
	  used_by_succ = analysis_rec (insn_p, bb_p->cfg_target, regT, level + 1);

	  if (used_by_succ != 0)
	    return used_by_succ;

	  /* Find the leaving instruction of ifcall.
	     In most cases, it is IFCRET, but some times, it may be J, JAL, etc.
	     If the leaving instruction is not IFCALL and JAL, this IFCALL wouldn't
	     return.  */
	  ifc_bb = bb_p->cfg_target;
	  while (leaving_reason == LRE_NONE && ifc_bb && ifc_bb->insn_tail)
	    {
	      func_mask = is_func_branch (ifc_bb->insn_tail->insn_num);

	      switch (func_mask)
		{
		case IS_COND_FUNC_CALL_MASK:
		  as_warn (_("Assembler cannot handle nested IFCALL."));
		case IS_COND_FUNC_RETURN_MASK:
		case IS_FUNC_CALL_MASK:
		  leaving_reason = LRE_RET;
		  break;
		default:
		  /* case IS_FUNC_RETURN_MASK: */
		  if (is_conditional_branch_instruction (ifc_bb->insn_tail->insn_num)
		      || is_direct_branch_instruction (ifc_bb->insn_tail->insn_num))
		    leaving_reason = LRE_NONRET;
		  break;
		}
	      ifc_bb = ifc_bb->list_next;
	    }

	  if (leaving_reason != LRE_NONRET)
	    {
	      ifc_mode = 0;
	      used_by_succ = analysis_rec (insn_p, bb_p->list_next, regT, level + 1);
	    }
	}
    }
  else if (func_mask == (int) IS_FUNC_CALL_MASK)
    {
      /* Update of register[0~5] can't be suppressed when function call since
	 these registers are used as function argument.  */
      if (regT > 5 && regT < 26)
	used_by_succ = analysis_rec (insn_p, bb_p->list_next, regT, level + 1);
      else if ((regT < 6 && regT >= 0) && bb_p->insn_tail->hint_func_args
	       && is_hint_func_args (bb_p->insn_tail->hint_func_args, regT))
	used_by_succ = analysis_rec (insn_p, bb_p->list_next, regT, level + 1);
      else
	{
	  if (bb_p->insn_tail->insn_num == NDS32_INSN_JAL)
	    {
	      used_by_succ = analysis_rec (insn_p, bb_p->cfg_target, regT, level + 1);
	      if (used_by_succ == 0)
		used_by_succ = analysis_rec (insn_p, bb_p->list_next, regT, level + 1);
	    }
	  else
	    return CGEN_OPINST_INPUT_MASK;
	}
    }

  return used_by_succ;
}

static int
analysis_rec (nds32_insn_instant *insn_p, basic_block *bb_p, int regT,
	      int level)
{
  nds32_insn_instant *insn_s;
  int finish, used_by_succ = 0;

  if (bb_p == NULL)
    return 0;

  /* Check if current basic block is reentrant.  */
  bb_p->walk_through++;
  if (bb_p->walk_through > 1)
    {
      /* For ifret case.  */
      if (bb_p->walk_through > 1
	  && bb_p->insn_head != NULL
	  && is_func_branch (bb_p->insn_tail->insn_num) == IS_COND_FUNC_RETURN_MASK
	  && !is_conservative_ifc && ifc_mode == 0)
	return analysis_rec (insn_p, bb_p->cfg_next, regT, level);
      /* Update those basic blocks visited in this path.  */
      if (bb_p->in_critical)
	bb_list_in_critical (nds32_path_bb_list);
      if (ifc_mode == 1
	  && is_func_branch (bb_p->insn_tail->insn_num) == IS_COND_FUNC_RETURN_MASK)
	ifc_mode = 0;
      /* Do nothing.  */
      return 0;
    }

  push_bb_to_bb_list (&nds32_use_bb_list, bb_p);

  /* For indirect branches, we assume it will be always used.  */
  if (level == 0xfffffff || bb_p == bb_indirect)
  {
    /* Rufus: Tag redundant sethi if the final insn is function call.  */
    if (regT > 14 && regT < 26)
      return 0;
    else
      return CGEN_OPINST_INPUT_MASK;
  }

  if (regT < 0 || regT > 31)
    {
      as_bad ("CFG : invalid register number of sethi\n");
      abort ();
    }

  push_bb_to_bb_list (&nds32_path_bb_list, bb_p);

  /* FIXME: the use_before_set only checks regT but no regTA here,
     additional regTA checks need to be introduced in the future.
     (especially for slt - beqz case).  */
  if (bb_p->set_before_use_gr[regT] != NULL)
    {
      if (is_func_branch (bb_p->insn_tail->insn_num) == IS_COND_FUNC_RETURN_MASK
	  && !is_conservative_ifc && ifc_mode == 1)
	ifc_mode = 0;
      pop_bb_from_bb_list (&nds32_path_bb_list);
      return CGEN_OPINST_OUTPUT_MASK;
    }
  else if (bb_p->use_before_set_gr[regT] != NULL)
    {
      insn_s = bb_p->use_before_set_gr[regT];
    }
  else
    {
      if (bb_p->insn_head == NULL)
	finish = analysis_rec (insn_p, bb_p->cfg_next, regT, level + 1);
      else
	finish = analysis_rec_bb (insn_p, bb_p, regT, level);
      pop_bb_from_bb_list (&nds32_path_bb_list);
      return finish;
    }

  /* regT is used before set in this basic block.  An instruction by instruction
     check can determine which instruction uses or sets it.  There may be 3
     kinds of results:
     (1) non-relaxable use before set: return CGEN_OPINST_INPUT_MASK
     (2) relaxable use before set: return CGEN_OPINST_OUTPUT_MASK
     (3) relaxable use with no set followed: return 0.  */
  finish = trace_bb_def_use (insn_p, insn_s, regT);

  if (!finish)
    used_by_succ = analysis_rec_bb (insn_p, bb_p, regT, level);

  if (is_func_branch (bb_p->insn_tail->insn_num) ==
      (int) IS_COND_FUNC_RETURN_MASK && !is_conservative_ifc && ifc_mode == 1)
    ifc_mode = 0;

  pop_bb_from_bb_list (&nds32_path_bb_list);

  if (!finish)
    return used_by_succ;
  else
    return finish;
}

static void
life_time_analysis_sethi (void)
{
  nds32_insn_list *insn_list = nds32_hi_insn_list;
  nds32_insn_instant *insn_s;
  int regT, finish = 0, used_by_succ = 0, fix_index, gen_tree, root_of_tree;
  symbolS *sym;
  valueT addend;
  reloc_tree_node *tree_node_t;

  while (insn_list != NULL)
    {
      ld_st_address_len_type = gen_tree = root_of_tree = 0;
      finish = used_by_succ = 0;
      prev_insn_num = 0;
      nds32_use_bb_list = NULL;
      insn_s = insn_list->insn;
      regT = check_insn_output_reg_valid (insn_s->gr_dep_list);

      fix_index = get_sym_addend_from_insn (insn_s, &sym, &addend);
      if (fix_index == insn_s->num_fixups)
	{
	  insn_list = insn_list->next;
	  continue;
	}
      current_trace_sym = sym;
      current_trace_addend = addend;

      switch (insn_s->fixups[fix_index]->fx_r_type)
	{
	case BFD_RELOC_NDS32_GOT_HI20:
	  current_reloc_type_mask = NDS32_GOT_MASK;
	  break;
	case BFD_RELOC_NDS32_GOTOFF_HI20:
	  current_reloc_type_mask = NDS32_GOTOFF_MASK;
	  break;
	case BFD_RELOC_NDS32_PLT_GOTREL_HI20:
	  current_reloc_type_mask = NDS32_PLT_GOT_MASK;
	  break;
	case BFD_RELOC_NDS32_GOTPC_HI20:
	  insert_relax_type (insn_s, BFD_RELOC_NDS32_LOADSTORE, 4, 0, NULL);
	  insn_list = insn_list->next;
	  continue;
	default:
	  current_reloc_type_mask = 0;
	}

      /* If sethi is not the tail instruction of the basic block, trace
	 the basic block it belongs to first.  Otherwise, directly trace
	 the fall through basic block and the branch target one.  */
      if (insn_s->next != NULL && insn_s->parent == insn_s->next->parent)
	finish = trace_bb_def_use (insn_s, insn_s->next, regT);
      push_bb_to_bb_list (&nds32_use_bb_list, insn_s->parent);

      if (!finish)
	{
	  used_by_succ = analysis_rec_bb (insn_s, insn_s->parent, regT, 0);
	  if (used_by_succ != CGEN_OPINST_INPUT_MASK)
	    {
	      insert_relax_type (insn_s, BFD_RELOC_NDS32_LOADSTORE, 4,
				 ld_st_address_len_type, NULL);
	      gen_tree = 1;
	    }
	}
      else if (finish == CGEN_OPINST_OUTPUT_MASK)
	{
	  insert_relax_type (insn_s, BFD_RELOC_NDS32_LOADSTORE, 4,
			     ld_st_address_len_type, NULL);
	  gen_tree = 1;
	}
      else if (finish == CGEN_OPINST_INPUT_MASK)
	{
	  /* Sethi will not be set to relaxation.  */
	}

      if (current_reloc_type_mask == NDS32_PLT_GOT_MASK)
	root_of_tree = 1;
      else if (current_reloc_type_mask == 0)
	{
	  tree_node_t = reloc_list_now;
	  while (tree_node_t)
	    {
	      if (!tree_node_t->child)
		break;
	      tree_node_t = tree_node_t->next;
	    }
	  if (!tree_node_t)
	    root_of_tree = 1;
	}

      if (gen_tree && root_of_tree && reloc_list_now)
	{
	  tree_node_t = new_reloc_node_sibling (NULL, insn_s);
	  if (current_reloc_type_mask == NDS32_PLT_GOT_MASK)
	    tree_node_t->type_mask = NDS32_PLT_GOT_MASK;
	  else
	    tree_node_t->type_mask = NDS32_MULCALL_MASK;
	  bind_reloc_list_insn (tree_node_t);
	  bind_reloc_node_child_sibling (tree_node_t, reloc_list_now);
	  while (reloc_list_now)
	    {
	      bind_reloc_list_insn (reloc_list_now);
	      reloc_list_now = reloc_list_now->sibling;
	    }
	}
      else
	free_reloc_node_sibling (&reloc_list_now);

      clean_temp_var_bb_list (nds32_use_bb_list);
      push_to_bb_list_all (&nds32_use_bb_list, &nds32_free_bb_list);
      push_to_bb_list_all (&nds32_path_bb_list, &nds32_free_bb_list);

      insn_list = insn_list->next;
    }
}

static int
life_time_analysis_ls_succ (nds32_insn_instant *insn_p)
{
  nds32_insn_instant *insn_s;
  int regT, finish = 0, used_by_succ = 0;
  nds32_bb_list *bak_path_bb_list = nds32_path_bb_list;
  nds32_bb_list *bak_use_bb_list = nds32_use_bb_list;
  int result = TRUE;

  save_temp_var_bb_list (nds32_use_bb_list);
  clean_temp_var_bb_list (nds32_use_bb_list);

  nds32_use_bb_list = NULL;
  nds32_path_bb_list = NULL;
  insn_s = insn_p;
  regT = check_insn_output_reg_valid (insn_s->gr_dep_list);

  if (insn_s->next != NULL && insn_s->parent == insn_s->next->parent)
    finish = trace_bb_def_use (insn_s, insn_s->next, regT);
  push_bb_to_bb_list (&nds32_use_bb_list, insn_s->parent);

  if (!finish)
    {
      used_by_succ = analysis_rec_bb (insn_s, insn_s->parent, regT, 0);
      if (used_by_succ == CGEN_OPINST_INPUT_MASK)
	result = FALSE;
    }
  else if (finish == CGEN_OPINST_OUTPUT_MASK)
    {
    }
  else if (finish == CGEN_OPINST_INPUT_MASK)
    {
      result = FALSE;
    }

  if (insn_p->parent->in_common)
    result = FALSE;

  if (!check_unknown_source_in_critical (nds32_use_bb_list))
    result = FALSE;

  /* See bug8315 and 87a1e3015.
     This line is moved after check_unknown_source_in_critical ().
     Otherwise, it always fails to relax sethi-ori-jral to jal.
     This statement was added in 87a1e301 by Rudolph,
     but I can't figure out why this is required to fix ifc issue.

     Besides, is_conservative_ifc is used by default now.  */
  insn_s->parent->in_critical = 1;

  clean_temp_var_bb_list (nds32_use_bb_list);
  push_to_bb_list_all (&nds32_use_bb_list, &nds32_free_bb_list);
  push_to_bb_list_all (&nds32_path_bb_list, &nds32_free_bb_list);

  nds32_path_bb_list = bak_path_bb_list;
  nds32_use_bb_list = bak_use_bb_list;
  restore_temp_var_bb_list (nds32_use_bb_list);
  return result;
}

static void
check_invalid_reloc (void)
{
  basic_block *bb;
  nds32_insn_instant *insn_t;
  reloc_tree_node *reloc_node_t, *reloc_node_t2;

  bb = bb_list;

  while (bb != NULL)
    {
      insn_t = bb->insn_head;
      while (insn_t != NULL && insn_t != bb->insn_tail->next)
	{
	  if (insn_t->reloc_node != NULL)
	    {
	      reloc_node_t = insn_t->reloc_node;
	      while (reloc_node_t)
		{
		  reloc_node_t2 = reloc_node_t;
		  reloc_node_t = reloc_node_t->next;
		  if (reloc_node_t != NULL
		      && reloc_node_t2->parent != reloc_node_t->parent)
		    {
		      if (enable_relax_warning)
			as_warn (_("%s: %d: Duplicate relaxation type found in the same instruction"),
				 reloc_node_t->insn->frag->fr_file,
				 reloc_node_t->insn->frag->fr_line);
		      reloc_node_t = insn_t->reloc_node;
		      while (reloc_node_t)
			{
			  taint_reloc_node_tree (reloc_node_t);
			  reloc_node_t = reloc_node_t->next;
			}
		      break;
		    }
		}
	      reloc_node_t = insn_t->reloc_node;
	      while (reloc_node_t)
		{
		  if (reloc_node_t->parent == NULL
		      && reloc_node_t->type_mask == NDS32_MULCALL_MASK
		      && reloc_node_t->leaf_num > relax_jal_bound)
		    taint_reloc_node_tree (reloc_node_t);
		  reloc_node_t = reloc_node_t->next;
		}
	    }
	  insn_t = insn_t->next;
	}
      bb = bb->list_next;
    }
}

static void
reloc_tree_turn_16_to_32_insn (reloc_tree_node *reloc_node_p)
{
  reloc_tree_node *reloc_node_t;
  fragS *frag_t;
  uint32_t insn;
  char *buf;

  if (reloc_node_p->tainted)
    return;

  if (reloc_node_p->child == NULL)
    {
      /* Check if leaf node is a relaxable 32 bit instruction
	 or a 16-bit instruction.  If yes, turn the instruction
	 to non-relaxable and 32-bit instruction.  */
      if (reloc_node_p->insn->byte_sz == 2
	  && reloc_node_p->insn->insn_sz == 4)
	{
	  /* (1) Turn 16-bit instruction to 32-bit.
	     (2) Clear Relaxable bit in frag->subtype.
	     (3) Turn frag->type to rs_fill.  */
	  frag_t = reloc_node_p->insn->frag;
	  /* Only jral5 converted here so no need to check if it is success.  */
	  convert_16_to_32 (frag_t, &insn);
	  buf = frag_t->fr_literal + frag_t->fr_fix - 2;
	  md_number_to_chars (buf, insn, 4);
	  frag_t->fr_fix += 2;
	  RELAX_CLEAR_RELAXABLE (frag_t);
	  frag_t->fr_type = rs_fill;
	  reloc_node_p->convertible = 1;
	  reloc_node_p->insn->byte_sz = 4;
	}
    }

  reloc_node_t = reloc_node_p->child;
  while (reloc_node_t)
    {
      reloc_tree_turn_16_to_32_insn (reloc_node_t);
      reloc_node_t = reloc_node_t->sibling;
    }
}

static void
adjust_reloc_contents (void)
{
  basic_block *bb;
  nds32_insn_instant *insn_t;
  reloc_tree_node *reloc_node_t;

  bb = bb_list;

  while (bb != NULL)
    {
      insn_t = bb->insn_head;
      while (insn_t != NULL && insn_t != bb->insn_tail->next)
	{
	  if (insn_t->reloc_node != NULL)
	    {
	      reloc_node_t = insn_t->reloc_node;

	      while (reloc_node_t != NULL)
		{
		  if (reloc_node_t->parent == NULL)
		    reloc_tree_turn_16_to_32_insn (reloc_node_t);
		  reloc_node_t = reloc_node_t->next;
		}
	    }
	  insn_t = insn_t->next;
	}
      bb = bb->list_next;
    }
}

static void
reloc_tree_gen_relocs (reloc_tree_node *reloc_node_p, int reloc_type)
{
  reloc_tree_node *reloc_node_t;
  static int pattern_level = 0;
  int i;

  if (reloc_node_p->tainted)
    return;

  if (reloc_node_p->child == NULL)
    {
      for (i = 0; i < pattern_level; i++)
	{
	  insert_nds32_fix_reloc_node (current_pattern[i], reloc_node_p,
				       BFD_RELOC_NDS32_PTR);
	}
      insert_relax_type_sym (reloc_node_p->insn, reloc_type,
			     reloc_node_p->insn->byte_sz, current_trace_sym,
			     current_trace_addend);
      if (reloc_type == BFD_RELOC_NDS32_MULCALL_SUFF
	  && (reloc_node_p->insn->insn_num == NDS32_INSN_MOV55
	      || reloc_node_p->insn->insn_num == NDS32_INSN_ORI))
	insert_relax_type_sym (reloc_node_p->insn,
			       BFD_RELOC_NDS32_PTR_RESOLVED,
			       reloc_node_p->insn->byte_sz, abs_section_sym,
			       2);
      else
	insert_relax_type_sym (reloc_node_p->insn,
			       BFD_RELOC_NDS32_PTR_RESOLVED,
			       reloc_node_p->insn->byte_sz, abs_section_sym,
			       0);
    }

  current_pattern[pattern_level] = reloc_node_p;
  pattern_level++;
  reloc_node_t = reloc_node_p->child;
  while (reloc_node_t)
    {
      reloc_tree_gen_relocs (reloc_node_t, reloc_type);
      reloc_node_t = reloc_node_t->sibling;
    }
  if (reloc_node_p->leaf_num)
    insert_relax_type (reloc_node_p->insn, BFD_RELOC_NDS32_PTR_COUNT, 0,
		       reloc_node_p->leaf_num, NULL);
  pattern_level--;
}

static void
append_relax_relocs (void)
{
  basic_block *bb;
  nds32_insn_instant *insn_t;
  reloc_tree_node *reloc_node_t;
  int converted = 0;

  bb = bb_list;

  while (bb != NULL)
    {
      insn_t = bb->insn_head;
      while (insn_t != NULL && insn_t != bb->insn_tail->next)
	{
	  if (insn_t->reloc_node != NULL)
	    {
	      reloc_node_t = insn_t->reloc_node;
	      converted = 0;

	      while (reloc_node_t != NULL)
		{
		  if (reloc_node_t->parent == NULL)
		    {
		      get_sym_addend_from_insn (reloc_node_t->insn,
						&current_trace_sym,
						&current_trace_addend);
		      switch (reloc_node_t->type_mask)
			{
			case NDS32_GOT_MASK:
			  reloc_tree_gen_relocs (reloc_node_t,
						 BFD_RELOC_NDS32_GOT_SUFF);
			  break;
			case NDS32_GOTOFF_MASK:
			  reloc_tree_gen_relocs (reloc_node_t,
						 BFD_RELOC_NDS32_GOTOFF_SUFF);
			  break;
			case NDS32_PLT_GOT_MASK:
			  reloc_tree_gen_relocs (reloc_node_t,
						 BFD_RELOC_NDS32_PLT_GOT_SUFF);
			  break;
			case NDS32_MULCALL_MASK:
			  reloc_tree_gen_relocs (reloc_node_t,
						 BFD_RELOC_NDS32_MULCALL_SUFF);
			  break;
			}
		    }
		  if (reloc_node_t->convertible && !converted)
		    {
		      insert_relax_type (reloc_node_t->insn,
					 BFD_RELOC_NDS32_INSN16, 4, 0, NULL);
		      converted = 1;
		    }
		  reloc_node_t = reloc_node_t->next;
		}
	    }
	  insn_t = insn_t->next;
	}
      bb = bb->list_next;
    }
}

static void
reloc_tree_trace_relocs_prefix (reloc_tree_node *reloc_node_p)
{
  reloc_tree_node *reloc_node_t;
  static int pattern_level = 0;
  int i;

  if (reloc_node_p->tainted)
    return;

  /* Count leaf number.  */
  if (reloc_node_p->child == NULL)
    for (i = 0; i < pattern_level; i++)
      current_pattern[i]->leaf_num++;

  current_pattern[pattern_level] = reloc_node_p;
  current_pattern[pattern_level]->leaf_num = 0;
  pattern_level++;
  reloc_node_t = reloc_node_p->child;
  while (reloc_node_t)
    {
      reloc_tree_trace_relocs_prefix (reloc_node_t);
      reloc_node_t = reloc_node_t->sibling;
    }
  pattern_level--;
}

static void
count_reloc_leaf (void)
{
  basic_block *bb;
  nds32_insn_instant *insn_t;
  reloc_tree_node *reloc_node_t;

  bb = bb_list;

  while (bb != NULL)
    {
      insn_t = bb->insn_head;
      while (insn_t != NULL && insn_t != bb->insn_tail->next)
	{
	  if (insn_t->reloc_node != NULL)
	    {
	      reloc_node_t = insn_t->reloc_node;

	      while (reloc_node_t != NULL)
		{
		  if (reloc_node_t->parent == NULL)
		    {
		      switch (reloc_node_t->type_mask)
			{
			case NDS32_GOT_MASK:
			case NDS32_GOTOFF_MASK:
			case NDS32_PLT_GOT_MASK:
			case NDS32_MULCALL_MASK:
			  reloc_tree_trace_relocs_prefix (reloc_node_t);
			  break;
			}
		    }
		  reloc_node_t = reloc_node_t->next;
		}
	    }
	  insn_t = insn_t->next;
	}
      bb = bb->list_next;
    }
}

static void
clean_reloc_trees (void)
{
  basic_block *bb;
  nds32_insn_instant *insn_t;

  bb = bb_list;
  while (bb != NULL)
    {
      insn_t = bb->insn_head;
      while (insn_t != NULL && insn_t != bb->insn_tail->next)
	{
	  free_reloc_node_next (insn_t->reloc_node);
	  insn_t = insn_t->next;
	}
      bb = bb->list_next;
    }
}

static void
cfg_clean (void)
{
  nds32_insn_instant *insn_s, *insn_s2;
  dep_node *node, *node2;
  basic_block *bb, *bb2;
  insn_label_list *label_list, *label_list2;
  nds32_bb_list *nds32_bb_list_l, *nds32_bb_list_l2;

  free_nds32_reloc_node_list (nds32_reloc_node_pool, NULL);
  free_nds32_insn_list (&nds32_hi_insn_list);
  free_nds32_insn_list (&nds32_got20_insn_list);
  free_nds32_insn_list (&nds32_slt_insn_list);
  free_nds32_insn_list (&nds32_ta_insn_list);
  free_nds32_insn_list (&nds32_free_insn_list);

  nds32_bb_list_l = nds32_free_bb_list;
  while (nds32_bb_list_l != NULL)
    {
      nds32_bb_list_l2 = nds32_bb_list_l->next;
      xfree (nds32_bb_list_l);
      nds32_bb_list_l = nds32_bb_list_l2;
    }

  if (bb_list == NULL)
    insn_s = NULL;
  else
    {
      bb = bb_list;
      while (bb != NULL && bb->insn_head == NULL)
	bb = bb->list_next;
      if (bb == NULL)
	insn_s = NULL;
      else
	insn_s = bb->insn_head;
    }
  while (insn_s != NULL)
    {
      node = insn_s->gr_dep_list;
      while (node != NULL)
	{
	  node2 = node->next;
	  xfree (node);
	  node = node2;
	}
      insn_s2 = insn_s->next;
      xfree (insn_s);
      insn_s = insn_s2;
    }
  bb = bb_list;
  while (bb != NULL)
    {
      label_list = bb->label_list;
      while (label_list != NULL)
	{
	  label_list2 = label_list->next;
	  xfree (label_list);
	  label_list = label_list2;
	}
      bb2 = bb->list_next;
      xfree (bb);
      bb = bb2;
    }
  clean_lp_bb_list (lp_bb_node_list);
  free (bb_indirect);
}

/* md_elf_section_change_hook  */

void
nds32_elf_section_change_hook (void)
{
  /* Reset b2bb_prev status.  See comments in md_assemble ().  */
  b2bb_prev = 0;

  /* If we have reached the end of a section and we are not on a word
     boundary then emit a nop to make sure that the section ends on a word
     boundary.  */
  if (seen_relaxable_p)
    (void) nds32_start_label (0, 1);

  /* In some cases a previous section may ended with a non-jump
     instruction because the previous section may integrated with
     another section in the other object with the same name.
     To avoid a cross-section basic block happened, a new basic
     block is needed when current section is changed.  */
  create_new_basic_block ();

  nds32_last_label = NULL;
}

/* md_cleanup  */

void
nds32_cleanup (void)
{
  /* If we have reached the end of a section and we are not on a word
     boundary then emit a nop to make sure that the section ends on a word
     boundary.  */
  if (seen_relaxable_p)
    (void) nds32_start_label (0, 1);
  create_new_basic_block ();
}

typedef struct LSDACS_entry LSDACS_entry;
typedef struct LSDA_entry LSDA_entry;
struct LSDACS_entry
{
  fragS *entries[4];
  LSDACS_entry *next;
};

struct LSDA_entry
{
  LSDACS_entry *lsdacs;
  fragS *pseudo_align_frag;
  int create_state;
  LSDA_entry *next;
};

/* This function is used to scan leb128 subtraction expressions,
   and insert fixups for them.

      e.g., .leb128  .L1 - .L0

   These expressions are heavily used in debug information or
   exception tables.  Because relaxation will change code size,
   we must resolve them in link time.  */

static void
nds32_insert_leb128_fixes (bfd *abfd ATTRIBUTE_UNUSED,
			   asection *sec, PTR xxx ATTRIBUTE_UNUSED)
{
  segment_info_type *seginfo = seg_info (sec);
  struct frag *fragP;

  subseg_set (sec, 0);

  for (fragP = seginfo->frchainP->frch_root;
       fragP; fragP = fragP->fr_next)
    {
      expressionS *exp;

      /* Only unsigned leb128 can be handle.  */
      if (fragP->fr_type != rs_leb128 || fragP->fr_subtype != 0
	  || fragP->fr_symbol == NULL)
	continue;

      exp = symbol_get_value_expression (fragP->fr_symbol);

      if (exp->X_op != O_subtract)
	continue;

      fix_new_exp (fragP, fragP->fr_fix, 0,
		   exp, 0, BFD_RELOC_NDS32_DIFF_ULEB128);
    }
}

void
md_end (void)
{
  frchainS *frchain_bak = frchain_now;
  segT seg_bak = now_seg;
  fragS *frag_bak = frag_now;
  int saved_endian = target_big_endian;

  if (enable_relax_relocs && bb_list != NULL)
    {
      bfdsym_hash = hash_new ();
      build_cfg ();
      bfd_map_over_sections (stdoutput, nds32_insert_leb128_fixes, NULL);
      count_bb_known_pred ();
      target_big_endian = 1;
      def_use_analysis ();
      life_time_analysis_sethi ();
      count_reloc_leaf ();
      check_invalid_reloc ();
      adjust_reloc_contents ();
      append_relax_relocs ();
      hash_traverse (bfdsym_hash, bfdsym_bb_map_delete);
      hash_die (bfdsym_hash);
    }

  push_to_insn_list_all (&nds32_hi_insn_list, &nds32_free_insn_list);
  clean_reloc_trees ();
  cfg_clean ();
  clean_seg_fixup_list ();

  frchain_now = frchain_bak;
  now_seg = seg_bak;
  frag_now = frag_bak;
  target_big_endian = saved_endian;

  if (vec_size == 4 || vec_size == 16)
    {
      unsigned int flag = 0;

      if (!sec_eflag)
	create_nds32_seg (NDS32_SEC_EFLAG_ISR);
      subseg_set (sec_eflag, (subsegT) 0);

      frag_more (4);
      frag_now->fr_fix += 4;
      flag |= vec_size == 4 ? 1 : 2;
      md_number_to_chars (frag_now->fr_literal, flag, 4);
    }
}

bfd_boolean
nds32_allow_local_subtract (expressionS *expr_l ATTRIBUTE_UNUSED,
			    expressionS *expr_r ATTRIBUTE_UNUSED,
			    segT sec ATTRIBUTE_UNUSED)
{
  return FALSE;
}

/* Sort relocation by address.

   We didn't use qsort () in stdlib, because quick-sort is not a stable
   sorting algorithm.  Relocations at the same address (r_offset) must keep
   their relative order.  For example, RELAX_ENTRY must be the very first
   relocation entry.

   Currently, this function implements insertion-sort.  */

static int
compar_relent (const void *lhs, const void *rhs)
{
  const arelent **l = (const arelent **) lhs;
  const arelent **r = (const arelent **) rhs;

  if ((*l)->address > (*r)->address)
    return 1;
  else if ((*l)->address == (*r)->address)
    return 0;
  else
    return -1;
}

/* SET_SECTION_RELOCS ()

   Although this macro is originally used to set a relocation for each section,
   we use it to sort relocations in the same section by the address of the
   relocation.  */

void
nds32_set_section_relocs (asection *sec, arelent ** relocs ATTRIBUTE_UNUSED,
			  unsigned int n ATTRIBUTE_UNUSED)
{
  bfd *abfd ATTRIBUTE_UNUSED = sec->owner;
  if (bfd_get_section_flags (abfd, sec) & (flagword) SEC_RELOC)
    nds32_insertion_sort (sec->orelocation, sec->reloc_count, sizeof (arelent**),
			  compar_relent);
}

static void
nds32_insert_relax_entry (bfd *abfd ATTRIBUTE_UNUSED, asection *sec,
			  PTR xxx ATTRIBUTE_UNUSED)
{
  segment_info_type *seginfo;
  fragS *fragP;
  fixS *fixP;
  expressionS exp;
  fixS *fix_tail_bak;
  fixS *fixp;

  seginfo = seg_info (sec);
  if (!seginfo || !symbol_rootP || !subseg_text_p (sec))
    return;
  /* If there is no relocation and relax is disabled, it is not necessary to
     insert R_NDS32_RELAX_ENTRY for linker do EX9 or IFC optimization.  */
  for (fixp = seginfo->fix_root; fixp; fixp = fixp->fx_next)
    if (!fixp->fx_done)
      break;
  if (!fixp && !enable_relax_ex9)
    return;

  subseg_change (sec, 0);
  fix_tail_bak = seginfo->fix_tail;

  /* Set RELAX_ENTRY flags for linker.  */
  fragP = seginfo->frchainP->frch_root;
  exp.X_op = O_symbol;
  exp.X_add_symbol = section_symbol (sec);
  exp.X_add_number = 0;
  if (!enable_relax_relocs)
    exp.X_add_number |= R_NDS32_RELAX_ENTRY_DISABLE_RELAX_FLAG;
  else
    {
      /* These flags are only enabled when global relax is enabled.
	 Maybe we can check DISABLE_RELAX_FLAG at linke-time,
	 so we set them anyway.  */
      if (enable_relax_ex9)
	exp.X_add_number |= R_NDS32_RELAX_ENTRY_EX9_FLAG;
      if (enable_relax_ifc)
	exp.X_add_number |= R_NDS32_RELAX_ENTRY_IFC_FLAG;
    }
  if (optimize)
    exp.X_add_number |= R_NDS32_RELAX_ENTRY_OPTIMIZE_FLAG;
  if (optimize_for_space)
    exp.X_add_number |= R_NDS32_RELAX_ENTRY_OPTIMIZE_FOR_SPACE_FLAG;
  if (optimize_for_space_no_align)
    exp.X_add_number |= R_NDS32_RELAX_ENTRY_OPTIMIZE_FOR_SPACE_UNALIGN_FLAG;
  fixP = fix_new_exp (fragP, 0, 0, &exp, 0, BFD_RELOC_NDS32_RELAX_ENTRY);
  fixP->fx_no_overflow = 1;

  if (fixP == seginfo->fix_root)
    fixP->fx_next = NULL;
  else
    fixP->fx_next = seginfo->fix_root;
  seginfo->fix_root = fixP;
  if (fix_tail_bak != NULL)
    fix_tail_bak->fx_next = NULL;
  seginfo->fix_tail = fix_tail_bak;
}

/* md_frob_file  */

void
nds32_frob_file (void)
{
  bfd_map_over_sections (stdoutput, nds32_insert_relax_entry, (char *) 0);
}

/* tc_fix_adjustable  */

bfd_boolean
nds32_fix_adjustable (fixS *fixP)
{
  bfd_reloc_code_real_type reloc_type;

  if ((int) fixP->fx_r_type >= (int) BFD_RELOC_UNUSED)
    {
      const CGEN_INSN *insn = NULL;
      int opindex;
      const CGEN_OPERAND *operand;

      opindex = (int) fixP->fx_r_type - (int) BFD_RELOC_UNUSED;
      operand = cgen_operand_lookup_by_num (gas_cgen_cpu_desc, opindex);
      reloc_type = md_cgen_lookup_reloc (insn, operand, fixP);
    }
  else
    reloc_type = fixP->fx_r_type;

  if (fixP->fx_addsy == NULL)
    return 1;

  /* Prevent all adjustments to global symbols.  */
  if (S_IS_EXTERNAL (fixP->fx_addsy))
    return 0;
  if (S_IS_WEAK (fixP->fx_addsy))
    return 0;

  if (pic_code && (reloc_type == BFD_RELOC_NDS32_20
		   || reloc_type == BFD_RELOC_NDS32_HI20
		   || reloc_type == BFD_RELOC_NDS32_LO12S3
		   || reloc_type == BFD_RELOC_NDS32_LO12S2
		   || reloc_type == BFD_RELOC_NDS32_LO12S2_DP
		   || reloc_type == BFD_RELOC_NDS32_LO12S2_SP
		   || reloc_type == BFD_RELOC_NDS32_LO12S1
		   || reloc_type == BFD_RELOC_NDS32_LO12S0
		   || reloc_type == BFD_RELOC_NDS32_LO12S0_ORI))
    return 0;

  if (reloc_type == BFD_RELOC_NDS32_GOT20
      || reloc_type == BFD_RELOC_NDS32_25_PLTREL
      || reloc_type == BFD_RELOC_NDS32_GOTPC_HI20
      || reloc_type == BFD_RELOC_NDS32_GOTPC_LO12
      || reloc_type == BFD_RELOC_NDS32_GOT_HI20
      || reloc_type == BFD_RELOC_NDS32_GOT_LO12)
    return 0;

  /* We need the symbol name for the VTABLE entries.  */
  if (reloc_type == BFD_RELOC_VTABLE_INHERIT
      || reloc_type == BFD_RELOC_VTABLE_ENTRY)
    return 0;

  return 1;
}

/* elf_tc_final_processing  */

void
elf_nds32_final_processing (void)
{
  /* An FPU_COM instruction is found without previous non-FPU_COM instruction.  */
  if (nds32_fpu_com
      && !(nds32_flags & (E_NDS32_HAS_FPU_INST | E_NDS32_HAS_FPU_DP_INST)))
    {
      /* Since only FPU_COM instructions are used and no other FPU
	 instructions are used.  The nds32_flag will be decided by
	 the enabled options by command line or default configuration.  */
      if (enable_fpu_dp_extension || enable_fpu_sp_extension)
	{
	  nds32_flags |= enable_fpu_dp_extension ? E_NDS32_HAS_FPU_DP_INST : 0;
	  nds32_flags |= enable_fpu_sp_extension ? E_NDS32_HAS_FPU_INST : 0;
	}
      else
	{
	  /* Should never here.  */
	  as_bad (_("Used FPU instructions requires enabling FPU extension"));
	}
    }

  if (nds32_flags & (E_NDS32_HAS_FPU_INST | E_NDS32_HAS_FPU_DP_INST))
    {
      /* single/double FPU has been used, set FPU register set
	 we did not check the actual number of register used
	 we may want to do it while assemble.  */
      nds32_flags &= ~E_NDS32_FPU_REG_CONF;
      nds32_flags |= fpu_config;
    }

  nds32_flags |= elf_ver | abi_ver;
  if (enable_reduce_regs)
    nds32_flags |= E_NDS32_HAS_REDUCED_REGS;
  if (pic_code)
    nds32_flags |= E_NDS32_HAS_PIC;

  elf_elfheader (stdoutput)->e_flags |= nds32_flags;
}

/* md_apply_fix  */

void
nds32_apply_fix (fixS *fixP, valueT *valP, segT seg ATTRIBUTE_UNUSED)
{
  char *where = fixP->fx_frag->fr_literal + fixP->fx_where;
  valueT value = *valP;
  /* Canonical name, since used a lot.  */

  if (fixP->fx_r_type < BFD_RELOC_UNUSED && fixP->fx_r_type > BFD_RELOC_NONE
      && fixP->fx_r_type != BFD_RELOC_NDS32_DIFF_ULEB128)
    {
      /* These are relocations we add not using CGEN.  */
      fixP->fx_addnumber = value;
      fixP->tc_fix_data = NULL;
      if (fixP->fx_r_type == BFD_RELOC_NDS32_DATA && !enable_relax_ex9)
	fixP->fx_done = 1;
      return;
    }

  if (fixP->fx_addsy == (symbolS *) NULL)
    fixP->fx_done = 1;

  if (fixP->fx_subsy != (symbolS *) NULL)
    {
      /* HOW DIFF RELOCATION WORKS.

	 First of all, this relocation is used to calculate the distance
	 between two symbols in the SAME section.  It is used for  jump-
	 table, debug information, exception table, et al.    Therefore,
	 it is a unsigned positive value.   It is NOT used for  general-
	 purpose arithmetic.

	 Consider this example,  the distance between  .LEND and .LBEGIN
	 is stored at the address of foo.

	 ---- >8 ---- >8 ---- >8 ---- >8 ----
	  .data
	  foo:
	    .word	.LBEGIN - .LEND

	  .text
	     [before]
	  .LBEGIN
			 \
	     [between]    distance
			 /
	  .LEND
	     [after]
	 ---- 8< ---- 8< ---- 8< ---- 8< ----

	 We use a single relocation entry for this expression.
	 * The initial distance value is stored direcly in that location
	   specified by r_offset (i.e., foo in this example.)
	 * The begin of the region, i.e., .LBEGIN, is specified by
	   r_info/R_SYM and r_addend, e.g., .text + 0x32.
	 * The end of region, i.e., .LEND, is represented by
	   .LBEGIN + distance instead of .LEND, so we only need
	   a single relocation entry instead of two.

	 When an instruction is relaxed, we adjust the relocation entry
	 depending on where the instruction locates.    There are three
	 cases, before, after and between the region.
	 * between: Distance value is read from r_offset,  adjusted and
	   written back into r_offset.
	 * before: Only r_addend is adjust.
	 * after: We don't care about it.

	 Hereby, there are some limitation.

	 `(.LEND - 1) - .LBEGIN' and `(.LEND - .LBEGIN) - 1'
	 are semantically different, and we cannot handle latter case
	 when relaxation.

	 The latter expression means subtracting 1 from the distance
	 between .LEND and .LBEGIN.  And the former expression means
	 the distance between (.LEND - 1) and .LBEGIN.

	 The nuance affects whether to adjust distance value when relax
	 an instruction.  In another words, whether the instruction
	 locates in the region.  Because we use a single relocation entry,
	 there is no field left for .LEND and the subtrahend.

	 Since GCC-4.5, GCC may produce debug information in such expression
	     .long  .L1-1-.L0
	 in order to describe register clobbering during an function-call.
	     .L0:
		call foo
	     .L1:

	 Check http://gcc.gnu.org/ml/gcc-patches/2009-06/msg01317.html
	 for details.

	 COLE  */

      value -= S_GET_VALUE (fixP->fx_subsy);
      *valP = value;
      fixP->fx_subsy = NULL;
      fixP->fx_offset -= value;

      switch (fixP->fx_r_type)
	{
	case BFD_RELOC_8:
	  fixP->fx_r_type = BFD_RELOC_NDS32_DIFF8;
	  md_number_to_chars (where, value, 1);
	  break;
	case BFD_RELOC_16:
	  fixP->fx_r_type = BFD_RELOC_NDS32_DIFF16;
	  md_number_to_chars (where, value, 2);
	  break;
	case BFD_RELOC_32:
	  fixP->fx_r_type = BFD_RELOC_NDS32_DIFF32;
	  md_number_to_chars (where, value, 4);
	  break;
	case BFD_RELOC_NDS32_DIFF_ULEB128:
	  /* cvt_frag_to_fill () has called output_leb128 () for us.  */
	  break;
	default:
	  as_bad_where (fixP->fx_file, fixP->fx_line, _("expression too complex"));
	  return;
	}
    }
  else if ((int) fixP->fx_r_type >= (int) BFD_RELOC_UNUSED)
    {
      CGEN_CPU_DESC cd = gas_cgen_cpu_desc;
      int opindex;
      const CGEN_OPERAND *operand;
      const char *errmsg;
      bfd_reloc_code_real_type reloc_type;
      CGEN_FIELDS *fields;
      const CGEN_INSN *insn;

      opindex = (int) fixP->fx_r_type - (int) BFD_RELOC_UNUSED;
      operand = cgen_operand_lookup_by_num (cd, opindex);
      fields = alloca (CGEN_CPU_SIZEOF_FIELDS (cd));
      insn = fixP->fx_cgen.insn;
      /* If the relocation has been fully resolved finish the operand here.  */
      /* FIXME: This duplicates the capabilities of code in BFD.  */
      if (fixP->fx_done
	  /* FIXME: If partial_inplace isn't set bfd_install_relocation won't
	     finish the job.  Testing for pcrel is a temporary hack.  */
	  || fixP->fx_pcrel)
	{
	  CGEN_CPU_SET_FIELDS_BITSIZE (cd) (fields, CGEN_INSN_BITSIZE (insn));
	  CGEN_CPU_SET_VMA_OPERAND (cd) (cd, opindex, fields,
					 (bfd_vma) value);

#if CGEN_INT_INSN_P
	  {
	    CGEN_INSN_INT insn_value;

	    insn_value = cgen_get_insn_value (cd, (unsigned char *) where,
					      CGEN_INSN_BITSIZE (insn));

	    /* ??? 0 is passed for `pc'.  */
	    errmsg = CGEN_CPU_INSERT_OPERAND (cd) (cd, opindex, fields,
						   &insn_value, (bfd_vma) 0);
	    cgen_put_insn_value (cd, (unsigned char *) where,
				 CGEN_INSN_BITSIZE (insn), insn_value);
	  }
#else
	  /* ??? 0 is passed for `pc'.  */
	  errmsg = CGEN_CPU_INSERT_OPERAND (cd) (cd, opindex, fields,
						 (unsigned char *) where,
						 (bfd_vma) 0);
#endif
	  if (errmsg)
	    as_bad_where (fixP->fx_file, fixP->fx_line, "%s", errmsg);
	}

      if (fixP->fx_done)
	return;

      /* The operand isn't fully resolved.  Determine a BFD reloc value
	 based on the operand information and leave it to
	 bfd_install_relocation.  Note that this doesn't work when
	 partial_inplace == false.  */

      reloc_type = md_cgen_lookup_reloc (insn, operand, fixP);

      if (reloc_type != BFD_RELOC_NONE)
	fixP->fx_r_type = reloc_type;
      else
	{
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("unresolved expression that must be resolved"));
	  fixP->fx_done = 1;
	  return;
	}
    }
  else if (fixP->fx_done)
    {
      /* We're finished with this fixup.  Install it because
	 bfd_install_relocation won't be called to do it.  */
      switch (fixP->fx_r_type)
	{
	case BFD_RELOC_8:
	  md_number_to_chars (where, value, 1);
	  break;
	case BFD_RELOC_16:
	  md_number_to_chars (where, value, 2);
	  break;
	case BFD_RELOC_32:
	  md_number_to_chars (where, value, 4);
	  break;
	case BFD_RELOC_64:
	  md_number_to_chars (where, value, 8);
	case BFD_RELOC_NDS32_MINUEND:
	  if (subseg_text_p (seg))
	    {
	      valueT val16;
	      val16 = md_chars_to_number (where, 2);
	      if ((val16 & INSN_LWI45_FE) != INSN_LWI45_FE)
		break;
	      val16 |= value;
	      md_number_to_chars (where, val16, 2);
	    }
	  break;
	default:
	  as_bad_where (fixP->fx_file, fixP->fx_line,
			_("internal error: can't install fix for reloc type %d (`%s')"),
			fixP->fx_r_type,
			bfd_get_reloc_code_name (fixP->fx_r_type));
	  break;
	}
    }
  /* else
     bfd_install_relocation will be called to finish things up.  */

  /* Tuck `value' away for use by tc_gen_reloc.
     See the comment describing fx_addnumber in write.h.
     This field is misnamed (or misused :-).  */
  fixP->fx_addnumber = value;
}

/* A BFD_ASSEMBLER GAS will call this to generate a relocation.  GAS will
   pass the resulting reloc to bfd_install_relocation.  This currently works
   poorly, as bfd_install_relocation often does the wrong thing, and
   instances of tc_gen_reloc have been written to work around the problems,
   which in turns makes it difficult to fix bfd_install_relocation.  */

arelent *
tc_gen_reloc (asection *section, fixS *fixP)
{
  arelent *reloc;
  bfd_reloc_code_real_type code;

  /* Remove LABEL relocation if it points to a 16-bit instruction and is not
     defined by .align directive.  */
  if (fixP->fx_r_type == BFD_RELOC_NDS32_LABEL)
    {
      if (subseg_text_p (section)
	  && fixP->fx_frag->fr_address + fixP->fx_where < section->size
	  && fixP->fx_offset < 2
	  && (fixP->fx_frag->fr_fix < 2
	      || (fixP->fx_frag->fr_fix > (fixP->fx_where + 1)
		  && 2 == get_frag_insn_size (fixP->fx_frag,
					      fixP->fx_where))))
	{
	  /* This is a 16-bit instruction, remove this relocation.  */
	  return NULL;
	}
    }

  reloc = (arelent *) xmalloc (sizeof (arelent));

  reloc->sym_ptr_ptr = (asymbol **) xmalloc (sizeof (asymbol *));
  *reloc->sym_ptr_ptr = symbol_get_bfdsym (fixP->fx_addsy);
  reloc->address = fixP->fx_frag->fr_address + fixP->fx_where;

  code = fixP->fx_r_type;
  if (pic_code)
    {
      switch (code)
	{
	case BFD_RELOC_NDS32_20:
	  if (fixP->fx_addsy != NULL
	      && strcmp (S_GET_NAME (fixP->fx_addsy), GOT_NAME) == 0)
	    code = BFD_RELOC_NDS32_GOTPC20;
	  else
	    code = BFD_RELOC_NDS32_GOT20;
	  break;
	case BFD_RELOC_NDS32_HI20:
	  if (fixP->fx_addsy != NULL
	      && strcmp (S_GET_NAME (fixP->fx_addsy), GOT_NAME) == 0)
	    code = BFD_RELOC_NDS32_GOTPC_HI20;
	  else
	    code = BFD_RELOC_NDS32_GOT_HI20;
	  break;
	case BFD_RELOC_NDS32_LO12S0:
	case BFD_RELOC_NDS32_LO12S0_ORI:
	  if (fixP->fx_addsy != NULL
	      && strcmp (S_GET_NAME (fixP->fx_addsy), GOT_NAME) == 0)
	    code = BFD_RELOC_NDS32_GOTPC_LO12;
	  else
	    code = BFD_RELOC_NDS32_GOT_LO12;
	  break;
	default:
	  break;
	}
    }

  reloc->howto = bfd_reloc_type_lookup (stdoutput, code);
  if (reloc->howto == (reloc_howto_type *) NULL)
    {
      as_bad_where (fixP->fx_file, fixP->fx_line,
		    _("internal error: can't export reloc type %d (`%s')"),
		    fixP->fx_r_type, bfd_get_reloc_code_name (code));
      return NULL;
    }

  /* Use fx_offset for these cases.  */
  if (fixP->fx_r_type == BFD_RELOC_VTABLE_ENTRY
      || fixP->fx_r_type == BFD_RELOC_VTABLE_INHERIT
      || fixP->fx_r_type == BFD_RELOC_NDS32_RELAX_ENTRY
      || fixP->fx_r_type == BFD_RELOC_NDS32_INSN16
      || fixP->fx_r_type == BFD_RELOC_NDS32_LABEL
      || fixP->fx_r_type == BFD_RELOC_NDS32_LONGCALL1
      || fixP->fx_r_type == BFD_RELOC_NDS32_LONGCALL2
      || fixP->fx_r_type == BFD_RELOC_NDS32_LONGCALL3
      || fixP->fx_r_type == BFD_RELOC_NDS32_LONGJUMP1
      || fixP->fx_r_type == BFD_RELOC_NDS32_LONGJUMP2
      || fixP->fx_r_type == BFD_RELOC_NDS32_LONGJUMP3
      || fixP->fx_r_type == BFD_RELOC_NDS32_LOADSTORE
      || fixP->fx_r_type == BFD_RELOC_NDS32_9_FIXED
      || fixP->fx_r_type == BFD_RELOC_NDS32_15_FIXED
      || fixP->fx_r_type == BFD_RELOC_NDS32_17_FIXED
      || fixP->fx_r_type == BFD_RELOC_NDS32_25_FIXED
      || fixP->fx_r_type == BFD_RELOC_NDS32_DIFF8
      || fixP->fx_r_type == BFD_RELOC_NDS32_DIFF16
      || fixP->fx_r_type == BFD_RELOC_NDS32_DIFF32
      || fixP->fx_r_type == BFD_RELOC_NDS32_DIFF_ULEB128)
    reloc->addend = fixP->fx_offset;
  else if ((!pic_code
	    && code != BFD_RELOC_NDS32_25_PLTREL)
	   && fixP->fx_pcrel
	   && fixP->fx_addsy != NULL
	   && (S_GET_SEGMENT (fixP->fx_addsy) != section)
	   && S_IS_DEFINED (fixP->fx_addsy)
	   && !S_IS_EXTERNAL (fixP->fx_addsy) && !S_IS_WEAK (fixP->fx_addsy))
    /* Already used fx_offset in the opcode field itself.  */
    reloc->addend = fixP->fx_offset;
  else if (fixP->fx_r_type == BFD_RELOC_NDS32_DATA)
    reloc->addend = fixP->fx_size;
  else
    reloc->addend = fixP->fx_addnumber;

  return reloc;
}

/* This function checks whether the "cont" is started with word "what".  */

static inline char *
nds32_end_of_match (char *cont, char *what)
{
  int len = strlen (what);

  if (strncasecmp (cont, what, len) == 0 && !is_part_of_name (cont[len]))
    return cont + len;

  return NULL;
}

/* md_parse_name ()

   This function is borrowed from tc-sh.c.  Sync it when upgrading.  */

int
nds32_parse_name (char const *name, expressionS * exprP, enum expr_mode mode,
		  char *nextcharP)
{
  char *next = input_line_pointer;
  char *next_end;
  int reloc_type;
  operatorT op_type;
  segT segment;

  exprP->X_op_symbol = NULL;
  exprP->X_md = BFD_RELOC_UNUSED;

  if (strcmp (name, GOT_NAME) == 0 && *nextcharP != '@')
    {
      if (!GOT_symbol)
	GOT_symbol = symbol_find_or_make (name);

      exprP->X_add_symbol = GOT_symbol;
no_suffix:
      /* If we have an absolute symbol or a
	 reg, then we know its value now.  */
      segment = S_GET_SEGMENT (exprP->X_add_symbol);
      if (mode != expr_defer && segment == absolute_section)
	{
	  exprP->X_op = O_constant;
	  exprP->X_add_number = S_GET_VALUE (exprP->X_add_symbol);
	  exprP->X_add_symbol = NULL;
	}
      else if (mode != expr_defer && segment == reg_section)
	{
	  exprP->X_op = O_register;
	  exprP->X_add_number = S_GET_VALUE (exprP->X_add_symbol);
	  exprP->X_add_symbol = NULL;
	}
      else
	{
	  exprP->X_op = O_symbol;
	  exprP->X_add_number = 0;
	}

      return 1;
    }

  exprP->X_add_symbol = symbol_find_or_make (name);

  if (*nextcharP != '@')
    goto no_suffix;
  else if ((next_end = nds32_end_of_match (next + 1, "GOTOFF")))
    {
      reloc_type = BFD_RELOC_NDS32_GOTOFF;
      op_type = O_PIC_reloc;
    }
  else if ((next_end = nds32_end_of_match (next + 1, "GOT")))
    {
      reloc_type = BFD_RELOC_NDS32_GOT20;
      op_type = O_PIC_reloc;
    }
  else if ((next_end = nds32_end_of_match (next + 1, "PLT")))
    {
      reloc_type = BFD_RELOC_NDS32_25_PLTREL;
      op_type = O_PIC_reloc;
    }
  else
    goto no_suffix;

  *input_line_pointer = *nextcharP;
  input_line_pointer = next_end;
  *nextcharP = *input_line_pointer;
  *input_line_pointer = '\0';

  exprP->X_op = op_type;
  exprP->X_add_number = 0;
  exprP->X_md = reloc_type;

  return 1;
}

/* md_cgen_record_fixup_exp  */

int
nds32_cgen_parse_fix_exp (int opinfo, expressionS *exp)
{
  /* Since machine independent part of assembler can't handle symbols with
     machine dependent operation(O_md1), and the RELAXABLE instructions make
     assembler handle instructions with symbol has operation O_md1, so a
     procedure which can turn machine dependent operation of symbol to machine
     independent operation is needed.

     For example:
     b SYM@PLT
     since b is an instruction with RELAXABLE attribute, and SYM@PLT is considered
     as a symbol with operation O_md1, O_md1 should be turned to O_symbol.  */

  if (exp->X_op == O_PIC_reloc && exp->X_md == BFD_RELOC_NDS32_25_PLTREL)
    {
      if (!pic_code)
	{
	  exp->X_op = O_symbol;
	  opinfo = exp->X_md;
	}
      else
	{
	  if (opinfo == 0)
	    {
	      exp->X_op = O_symbol;
	      opinfo = exp->X_md;
	    }
	  else
	    {
	      exp->X_op = O_symbol;
	    }
	}
    }

  return opinfo;
}

int
tc_nds32_regname_to_dw2regnum (char *regname)
{
  symbolS *sym = symbol_find (regname);

  if (S_GET_SEGMENT (sym) == reg_section
      && sym->sy_value.X_add_number < 32)
    return sym->sy_value.X_add_number;
  return -1;
}

void
tc_nds32_frame_initial_instructions (void)
{
  /* CIE */
  cfi_add_CFA_def_cfa (REG_SP, 0);
}
