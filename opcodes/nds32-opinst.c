/* Semantic operand instances for nds32.

THIS FILE IS MACHINE GENERATED WITH CGEN.

Copyright 1996-2010 Free Software Foundation, Inc.

This file is part of the GNU Binutils and/or GDB, the GNU debugger.

   This file is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 3, or (at your option)
   any later version.

   It is distributed in the hope that it will be useful, but WITHOUT
   ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
   or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
   License for more details.

   You should have received a copy of the GNU General Public License along
   with this program; if not, write to the Free Software Foundation, Inc.,
   51 Franklin Street - Fifth Floor, Boston, MA 02110-1301, USA.

*/

#include "sysdep.h"
#include "ansidecl.h"
#include "bfd.h"
#include "symcat.h"
#include "nds32-desc.h"
#include "nds32-opc.h"

/* Operand references.  */

#define OP_ENT(op) NDS32_OPERAND_##op
#define INPUT CGEN_OPINST_INPUT
#define OUTPUT CGEN_OPINST_OUTPUT
#define END CGEN_OPINST_END
#define COND_REF CGEN_OPINST_COND_REF

static const CGEN_OPINST sfmt_empty_ops[] ATTRIBUTE_UNUSED = {
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_movi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "slo20", HW_H_SLO20, CGEN_MODE_INT, OP_ENT (SLO20), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sethi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "uhi20", HW_H_UHI20, CGEN_MODE_UINT, OP_ENT (UHI20), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_addi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_add_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_subri_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_andi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "ulo15", HW_H_ULO15, CGEN_MODE_UINT, OP_ENT (ULO15), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_and_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_seb_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_slli_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "uimm5", HW_H_UIMM5, CGEN_MODE_UINT, OP_ENT (UIMM5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_srli_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, COND_REF },
  { INPUT, "uimm5", HW_H_UIMM5, CGEN_MODE_UINT, OP_ENT (UIMM5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mults64_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, COND_REF },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, COND_REF },
  { OUTPUT, "rd1", HW_H_ACCUM, CGEN_MODE_UDI, OP_ENT (RD1), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_madds64_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, COND_REF },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, COND_REF },
  { INPUT, "rd1", HW_H_ACCUM, CGEN_MODE_UDI, OP_ENT (RD1), 0, COND_REF },
  { OUTPUT, "rd1", HW_H_ACCUM, CGEN_MODE_UDI, OP_ENT (RD1), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mult32_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rd1", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, COND_REF },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, COND_REF },
  { OUTPUT, "h_accum_hl_USI_sll__INT_index_of__INT_rd1_1", HW_H_ACCUM_HL, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_madd32_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rd1", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_accum_hl_USI_sll__INT_index_of__INT_rd1_1", HW_H_ACCUM_HL, CGEN_MODE_USI, 0, 0, COND_REF },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, COND_REF },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, COND_REF },
  { OUTPUT, "h_accum_hl_USI_sll__INT_index_of__INT_rd1_1", HW_H_ACCUM_HL, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mfusr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "groupidx", HW_H_GROUP, CGEN_MODE_UINT, OP_ENT (GROUPIDX), 0, 0 },
  { INPUT, "usridx", HW_H_USR, CGEN_MODE_UINT, OP_ENT (USRIDX), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mtusr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "groupidx", HW_H_GROUP, CGEN_MODE_UINT, OP_ENT (GROUPIDX), 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "usridx", HW_H_USR, CGEN_MODE_UINT, OP_ENT (USRIDX), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lbi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_UQI_add__USI_ra5_slo15b", HW_H_MEMORY, CGEN_MODE_UQI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15b", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15B), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lbi_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UQI_ra5", HW_H_MEMORY, CGEN_MODE_UQI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15b", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15B), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lb_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UQI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_UQI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lb_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UQI_ra5", HW_H_MEMORY, CGEN_MODE_UQI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UHI_add__USI_ra5_slo15h", HW_H_MEMORY, CGEN_MODE_UHI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15h", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15H), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhi_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UHI_ra5", HW_H_MEMORY, CGEN_MODE_UHI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15h", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15H), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lh_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UHI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_UHI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lh_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UHI_ra5", HW_H_MEMORY, CGEN_MODE_UHI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_USI_add__USI_ra5_slo15w", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15w", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15W), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_USI_ra5", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15w", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15W), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lw_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_USI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lw_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_USI_ra5", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swup_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "h_memory_USI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lbsi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_QI_add__USI_ra5_slo15b", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15b", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15B), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lbsi_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_QI_ra5", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15b", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15B), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lbs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_QI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lbs_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_QI_ra5", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhsi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_HI_add__USI_ra5_slo15h", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15h", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15H), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhsi_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_HI_ra5", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15h", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15H), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_HI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhs_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_HI_ra5", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sbi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo15b", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15B), 0, 0 },
  { OUTPUT, "h_memory_QI_add__USI_ra5_slo15b", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sbi_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo15b", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15B), 0, 0 },
  { OUTPUT, "h_memory_QI_ra5", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sb_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "h_memory_QI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sb_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "h_memory_QI_ra5", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_shi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo15h", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15H), 0, 0 },
  { OUTPUT, "h_memory_HI_add__USI_ra5_slo15h", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_shi_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo15h", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15H), 0, 0 },
  { OUTPUT, "h_memory_HI_ra5", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sh_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "h_memory_HI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sh_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "h_memory_HI_ra5", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo15w", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15W), 0, 0 },
  { OUTPUT, "h_memory_SI_add__USI_ra5_slo15w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swi_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo15w", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15W), 0, 0 },
  { OUTPUT, "h_memory_SI_ra5", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sw_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "h_memory_SI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sw_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "h_memory_SI_ra5", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { OUTPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lmw_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "mask4", HW_H_MASK4, CGEN_MODE_UINT, OP_ENT (MASK4), 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_llw_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_SI_addr", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_scw_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_j_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "disp24", HW_H_DISP24, CGEN_MODE_INT, OP_ENT (DISP24), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_jr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_4", HW_H_GR, CGEN_MODE_USI, 0, 4, COND_REF },
  { INPUT, "h_gr_USI_c_code__SI_H_GR_LP", HW_H_GR, CGEN_MODE_USI, 0, 0, COND_REF },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "h_memory_SI_add__USI_reg__USI_h_gr_4_4", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, COND_REF },
  { OUTPUT, "h_memory_SI_add__USI_reg__USI_h_gr_4_8", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, COND_REF },
  { OUTPUT, "h_memory_SI_reg__USI_h_gr_4", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, COND_REF },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ret_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_jr_itoff_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "h_sr_USI_c_code__SI_H_SR_PSW", HW_H_SR, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_jral_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_jral_iton_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "h_sr_USI_c_code__SI_H_SR_PSW", HW_H_SR, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_beq_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "disp14", HW_H_DISP14, CGEN_MODE_INT, OP_ENT (DISP14), 0, COND_REF },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_beqz_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "disp16", HW_H_DISP16, CGEN_MODE_INT, OP_ENT (DISP16), 0, COND_REF },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mfsr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "sr10", HW_H_SR, CGEN_MODE_USI, OP_ENT (SR10), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mtsr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { OUTPUT, "sr10", HW_H_SR, CGEN_MODE_USI, OP_ENT (SR10), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_setend_l_ops[] ATTRIBUTE_UNUSED = {
  { OUTPUT, "h_sr_USI_c_code__SI_H_SR_PSW", HW_H_SR, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_cmovz_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, COND_REF },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_dprefi_d_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "dprefst", HW_H_DPREFST, CGEN_MODE_UINT, OP_ENT (DPREFST), 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15d", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15D), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_dprefi_w_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "dprefst", HW_H_DPREFST, CGEN_MODE_UINT, OP_ENT (DPREFST), 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "slo15w", HW_H_SLO15, CGEN_MODE_INT, OP_ENT (SLO15W), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_dpref_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "dprefst", HW_H_DPREFST, CGEN_MODE_UINT, OP_ENT (DPREFST), 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_isync_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_msync_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "msyncst", HW_H_MSYNCST, CGEN_MODE_UINT, OP_ENT (MSYNCST), 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_isb_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_dsb_ops[] ATTRIBUTE_UNUSED = {
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_standby_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { INPUT, "standbyst", HW_H_STANDBYST, CGEN_MODE_UINT, OP_ENT (STANDBYST), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_trap_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "swid15", HW_H_SWID15, CGEN_MODE_UINT, OP_ENT (SWID15), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_teqz_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "swid15", HW_H_SWID15, CGEN_MODE_UINT, OP_ENT (SWID15), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_tlbop_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32t4_ext5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_cctl_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32t4_ext5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32tx_1_21", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_abs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, COND_REF },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ave_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_min_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_clo_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_bse_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_pbsad_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_pbsada_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mov55_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { INPUT, "ra5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5H), 0, COND_REF },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { OUTPUT, "rt5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5H), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_movi55_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "simm5h", HW_H_SIMM5H, CGEN_MODE_INT, OP_ENT (SIMM5H), 0, 0 },
  { OUTPUT, "rt5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5H), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_addi45_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "imm5u", HW_H_UIMM5H, CGEN_MODE_UINT, OP_ENT (IMM5U), 0, 0 },
  { INPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { OUTPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_add45_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "rb5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5H), 0, 0 },
  { INPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { OUTPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_srai45_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { INPUT, "uimm5h", HW_H_UIMM5H, CGEN_MODE_UINT, OP_ENT (UIMM5H), 0, 0 },
  { OUTPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_srli45_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_16_rt4", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, COND_REF },
  { INPUT, "uimm5h", HW_H_UIMM5H, CGEN_MODE_UINT, OP_ENT (UIMM5H), 0, 0 },
  { OUTPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_slli333_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "uimm3", HW_H_UIMM3, CGEN_MODE_UINT, OP_ENT (UIMM3), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_seb33_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_add333_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "rb3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RB3), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi333_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_SI_add__USI_ra3_ulo3w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "ulo3w", HW_H_ULO3W, CGEN_MODE_UINT, OP_ENT (ULO3W), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi333_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_SI_ra3", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "ulo3w", HW_H_ULO3W, CGEN_MODE_UINT, OP_ENT (ULO3W), 0, 0 },
  { OUTPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhi333_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UHI_add__USI_ra3_ulo3h", HW_H_MEMORY, CGEN_MODE_UHI, 0, 0, 0 },
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "ulo3h", HW_H_ULO3H, CGEN_MODE_UINT, OP_ENT (ULO3H), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lbi333_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_UQI_add__USI_ra3_ulo3b", HW_H_MEMORY, CGEN_MODE_UQI, 0, 0, 0 },
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "ulo3b", HW_H_ULO3B, CGEN_MODE_UINT, OP_ENT (ULO3B), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swi333_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { INPUT, "ulo3w", HW_H_ULO3W, CGEN_MODE_UINT, OP_ENT (ULO3W), 0, 0 },
  { OUTPUT, "h_memory_SI_add__USI_ra3_ulo3w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swi333_bi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { INPUT, "ulo3w", HW_H_ULO3W, CGEN_MODE_UINT, OP_ENT (ULO3W), 0, 0 },
  { OUTPUT, "h_memory_SI_ra3", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { OUTPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_shi333_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { INPUT, "ulo3h", HW_H_ULO3H, CGEN_MODE_UINT, OP_ENT (ULO3H), 0, 0 },
  { OUTPUT, "h_memory_HI_add__USI_ra3_ulo3h", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sbi333_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { INPUT, "ulo3b", HW_H_ULO3B, CGEN_MODE_UINT, OP_ENT (ULO3B), 0, 0 },
  { OUTPUT, "h_memory_QI_add__USI_ra3_ulo3b", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi450_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_memory_SI_ra5h", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { INPUT, "ra5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5H), 0, 0 },
  { OUTPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swi450_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5H), 0, 0 },
  { INPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { OUTPUT, "h_memory_SI_ra5h", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi37_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_FP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_SI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_FP_ulo7w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { INPUT, "ulo7w", HW_H_ULO7W, CGEN_MODE_UINT, OP_ENT (ULO7W), 0, 0 },
  { OUTPUT, "rt3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swi37_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_FP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rt3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3), 0, 0 },
  { INPUT, "ulo7w", HW_H_ULO7W, CGEN_MODE_UINT, OP_ENT (ULO7W), 0, 0 },
  { OUTPUT, "h_memory_SI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_FP_ulo7w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_beqz38_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "hsdisp8", HW_H_HSDISP8, CGEN_MODE_INT, OP_ENT (HSDISP8), 0, COND_REF },
  { INPUT, "rt3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_beqs38_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_5", HW_H_GR, CGEN_MODE_USI, 0, 5, 0 },
  { INPUT, "hsdisp8", HW_H_HSDISP8, CGEN_MODE_INT, OP_ENT (HSDISP8), 0, COND_REF },
  { INPUT, "rt3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_j8_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "hsdisp8", HW_H_HSDISP8, CGEN_MODE_INT, OP_ENT (HSDISP8), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_jr5_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rb5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5H), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_slti45_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { INPUT, "uimm5h", HW_H_UIMM5H, CGEN_MODE_UINT, OP_ENT (UIMM5H), 0, 0 },
  { OUTPUT, "h_gr_USI_15", HW_H_GR, CGEN_MODE_USI, 0, 15, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_slt45_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "rb5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5H), 0, 0 },
  { INPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { OUTPUT, "h_gr_USI_15", HW_H_GR, CGEN_MODE_USI, 0, 15, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_beqzs8_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_15", HW_H_GR, CGEN_MODE_USI, 0, 15, 0 },
  { INPUT, "hsdisp8", HW_H_HSDISP8, CGEN_MODE_INT, OP_ENT (HSDISP8), 0, COND_REF },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_break16_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "swid9", HW_H_SWID9, CGEN_MODE_UINT, OP_ENT (SWID9), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_addi10_sp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_SP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "simm10", HW_H_SIMM10H, CGEN_MODE_INT, OP_ENT (SIMM10), 0, 0 },
  { OUTPUT, "h_gr_USI_c_code__SI_H_GR_SP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi37_sp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_SP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_SI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_SP_ulo7w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { INPUT, "ulo7w", HW_H_ULO7W, CGEN_MODE_UINT, OP_ENT (ULO7W), 0, 0 },
  { OUTPUT, "rt3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swi37_sp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_SP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rt3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3), 0, 0 },
  { INPUT, "ulo7w", HW_H_ULO7W, CGEN_MODE_UINT, OP_ENT (ULO7W), 0, 0 },
  { OUTPUT, "h_memory_SI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_SP_ulo7w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_bmski33_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, COND_REF },
  { INPUT, "uimm3_10", HW_H_UIMM3_10, CGEN_MODE_UINT, OP_ENT (UIMM3_10), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_addri36_sp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_SP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "uimm6w", HW_H_UIMM6W, CGEN_MODE_UINT, OP_ENT (UIMM6W), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi45_fe_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_R8", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_R8_simm5w", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "simm5w", HW_H_SIMM5W, CGEN_MODE_INT, OP_ENT (SIMM5W), 0, 0 },
  { OUTPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mul33_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra3", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RA3), 0, 0 },
  { INPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { OUTPUT, "rt3_7", HW_H_GR8, CGEN_MODE_USI, OP_ENT (RT3_7), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_movpi45_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "suimm5", HW_H_SUIMM5, CGEN_MODE_UINT, OP_ENT (SUIMM5), 0, 0 },
  { OUTPUT, "rt4", HW_H_GR16, CGEN_MODE_USI, OP_ENT (RT4), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_push25_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "reglist", HW_H_REGLIST, CGEN_MODE_UINT, OP_ENT (REGLIST), 0, 0 },
  { INPUT, "uimm5d", HW_H_UIMM5D, CGEN_MODE_UINT, OP_ENT (UIMM5D), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_pop25_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_LP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "reglist", HW_H_REGLIST, CGEN_MODE_UINT, OP_ENT (REGLIST), 0, 0 },
  { INPUT, "uimm5d", HW_H_UIMM5D, CGEN_MODE_UINT, OP_ENT (UIMM5D), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_movd44_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_16_ra5e", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_16_rt5e", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_add5_pc_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rb5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5H), 0, 0 },
  { OUTPUT, "rb5h", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5H), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_break16v3_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "swid9", HW_H_SWID9, CGEN_MODE_UINT, OP_ENT (SWID9), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_addi_gp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_GP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "slo19", HW_H_SLO19, CGEN_MODE_INT, OP_ENT (SLO19), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_maddr32_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mulr64_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "h_gr_USI_and__INT_index_of__INT_rt5_4294967294", HW_H_GR, CGEN_MODE_USI, 0, 0, COND_REF },
  { OUTPUT, "h_gr_USI_or__INT_index_of__INT_rt5_1", HW_H_GR, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sbi_gp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_GP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo19", HW_H_SLO19, CGEN_MODE_INT, OP_ENT (SLO19), 0, 0 },
  { OUTPUT, "h_memory_QI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_GP_slo19", HW_H_MEMORY, CGEN_MODE_QI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_shi_gp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_GP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo18h", HW_H_SLO18, CGEN_MODE_INT, OP_ENT (SLO18H), 0, 0 },
  { OUTPUT, "h_memory_HI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_GP_slo18h", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_swi_gp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_GP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "slo17w", HW_H_SLO17, CGEN_MODE_INT, OP_ENT (SLO17W), 0, 0 },
  { OUTPUT, "h_memory_SI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_GP_slo17w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lbi_gp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_GP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_UQI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_GP_slo19", HW_H_MEMORY, CGEN_MODE_UQI, 0, 0, 0 },
  { INPUT, "slo19", HW_H_SLO19, CGEN_MODE_INT, OP_ENT (SLO19), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhi_gp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_GP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_UHI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_GP_slo18h", HW_H_MEMORY, CGEN_MODE_UHI, 0, 0, 0 },
  { INPUT, "slo18h", HW_H_SLO18, CGEN_MODE_INT, OP_ENT (SLO18H), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lhsi_gp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_GP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_HI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_GP_slo18h", HW_H_MEMORY, CGEN_MODE_HI, 0, 0, 0 },
  { INPUT, "slo18h", HW_H_SLO18, CGEN_MODE_INT, OP_ENT (SLO18H), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_lwi_gp_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_gr_USI_c_code__SI_H_GR_GP", HW_H_GR, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_SI_add__USI_reg__USI_h_gr_c_code__SI_H_GR_GP_slo17w", HW_H_MEMORY, CGEN_MODE_SI, 0, 0, 0 },
  { INPUT, "slo17w", HW_H_SLO17, CGEN_MODE_INT, OP_ENT (SLO17W), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_divr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rs5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, COND_REF },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "rs5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RS5), 0, COND_REF },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_sbup_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { OUTPUT, "h_memory_UQI_add__USI_ra5_sll__USI_rb5_si", HW_H_MEMORY, CGEN_MODE_UQI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_beqc_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "disp8", HW_H_DISP8, CGEN_MODE_INT, OP_ENT (DISP8), 0, COND_REF },
  { INPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { INPUT, "simm11", HW_H_SLO11, CGEN_MODE_INT, OP_ENT (SIMM11), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_jralnez_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_jrnez_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_add_slli_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { INPUT, "ulo5", HW_H_ULO5, CGEN_MODE_UINT, OP_ENT (ULO5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_bitci_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "ulo15", HW_H_ULO15, CGEN_MODE_UINT, OP_ENT (ULO15), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_aaddl_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "rc5_0_a", HW_H_GR_EVEN, CGEN_MODE_USI, OP_ENT (RC5_0_A), 0, 0 },
  { OUTPUT, "rc5_1_a", HW_H_GR_ODD, CGEN_MODE_USI, OP_ENT (RC5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ala_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { OUTPUT, "dh2_16_a", HW_H_AR_ACCUM1, CGEN_MODE_USI, OP_ENT (DH2_16_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_alr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_alr2_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_asa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_dh2_16_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_asr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_aupi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amfar_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "aridx5_a", HW_H_AI_ARIDX5, CGEN_MODE_UINT, OP_ENT (ARIDX5_A), 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "rd5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RD5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtar_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "aridx5_a", HW_H_AI_ARIDX5, CGEN_MODE_UINT, OP_ENT (ARIDX5_A), 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtari_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "aridx4_a", HW_H_AI_ARIDX4, CGEN_MODE_UINT, OP_ENT (ARIDX4_A), 0, 0 },
  { INPUT, "imm16_a", HW_H_AI_IMM16, CGEN_MODE_UHI, OP_ENT (IMM16_A), 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_asats48_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, COND_REF },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_awext_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "lsbloc_a", HW_H_AI_LSBLOC, CGEN_MODE_UINT, OP_ENT (LSBLOC_A), 0, 0 },
  { OUTPUT, "rd5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RD5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amadd_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amaddl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amaddl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amaddl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10B5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amaddl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10B5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amaddsa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amnegs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amnegsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amnegsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amnegsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10B5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amnegsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10B5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amnegssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_azol_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "h_ar_lb_USI", HW_H_AR_LB, CGEN_MODE_USI, 0, 0, COND_REF },
  { INPUT, "h_ar_lc_UHI", HW_H_AR_LC, CGEN_MODE_UHI, 0, 0, 0 },
  { OUTPUT, "h_ar_lc_UHI", HW_H_AR_LC, CGEN_MODE_UHI, 0, 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabbs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabts_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amatbs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amatts_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambbs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambts_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtbs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtts_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabbsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabbsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10A5_A_B), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabbsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabbsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10A5_A_B), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabbssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabtsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabtsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10A5_A_B), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabtsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabtsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10A5_A_B), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amabtssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amatbsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amatbsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10A5_A_T), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amatbsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amatbsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10A5_A_T), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amatbssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amattsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amattsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10A5_A_T), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amattsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amattsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10A5_A_T), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amattssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambbsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambbsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10A5_A_B), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambbsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambbsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10A5_A_B), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambbssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambtsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambtsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10A5_A_B), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambtsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambtsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10A5_A_B), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ambtssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RA5_A_B), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtbsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtbsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10A5_A_T), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtbsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtbsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10A5_A_T), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtbssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amttsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amttsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10A5_A_T), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amttsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amttsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10A5_A_T), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amttssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RA5_A_T), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawbs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawts_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwbs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwts_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawbsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawbsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawbsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawbsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawbssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawtsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawtsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawtsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawtsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amawtssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwbsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwbsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwbsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwbsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a_b", HW_H_GR_LO_BOTTOM, CGEN_MODE_USI, OP_ENT (R10B5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwbssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_b", HW_H_GR_BOTTOM, CGEN_MODE_USI, OP_ENT (RB5_A_B), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwtsl_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwtsl_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { OUTPUT, "r10c5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10C5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwtsl2_s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { OUTPUT, "rb5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwtsl2_l_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_0_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im6_i_1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr0", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "h_memory_USI_adm_vaddr1", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { INPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, COND_REF },
  { INPUT, "im6_m_0_a", HW_H_AR_M_LO, CGEN_MODE_HI, OP_ENT (IM6_M_0_A), 0, COND_REF },
  { INPUT, "im6_m_1_a", HW_H_AR_M_HI, CGEN_MODE_HI, OP_ENT (IM6_M_1_A), 0, COND_REF },
  { INPUT, "r10a5_a", HW_H_GR_LO, CGEN_MODE_USI, OP_ENT (R10A5_A), 0, 0 },
  { INPUT, "r10b5_a_t", HW_H_GR_LO_TOP, CGEN_MODE_USI, OP_ENT (R10B5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "im6_i_0_a", HW_H_AR_I_LO, CGEN_MODE_UHI, OP_ENT (IM6_I_0_A), 0, 0 },
  { OUTPUT, "im6_i_1_a", HW_H_AR_I_HI, CGEN_MODE_UHI, OP_ENT (IM6_I_1_A), 0, 0 },
  { OUTPUT, "r10c5_0_a", HW_H_GR_LO_EVEN, CGEN_MODE_USI, OP_ENT (R10C5_0_A), 0, 0 },
  { OUTPUT, "r10c5_1_a", HW_H_GR_LO_ODD, CGEN_MODE_USI, OP_ENT (R10C5_1_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amwtssa_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_d1_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_dh2_6_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_im5_i_a", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, COND_REF },
  { INPUT, "im5_m_a", HW_H_AR_M, CGEN_MODE_HI, OP_ENT (IM5_M_A), 0, COND_REF },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { INPUT, "rb5_a_t", HW_H_GR_TOP, CGEN_MODE_USI, OP_ENT (RB5_A_T), 0, 0 },
  { OUTPUT, "d1_a", HW_H_AR_ACCUM, CGEN_MODE_UDI, OP_ENT (D1_A), 0, 0 },
  { OUTPUT, "h_memory_USI_adm_vaddr", HW_H_MEMORY, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "im5_i_a", HW_H_AR_I, CGEN_MODE_UHI, OP_ENT (IM5_I_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amfar2_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ar2idx5_a", HW_H_AI_AR2IDX5, CGEN_MODE_UINT, OP_ENT (AR2IDX5_A), 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "rd5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RD5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_amtar2_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "aridx5_a", HW_H_AI_ARIDX5, CGEN_MODE_UINT, OP_ENT (ARIDX5_A), 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5_a", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5_A), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fls_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_flsi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "slo12w", HW_H_SLO12, CGEN_MODE_INT, OP_ENT (SLO12W), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fmfcfg_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fmfsr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fs2d_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fabss_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fadds_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fcmpeqs_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fabsd_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_faddd_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fcmovnd_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fd2s_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fld_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fldi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "slo12d", HW_H_SLO12, CGEN_MODE_INT, OP_ENT (SLO12D), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_fmfdr_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_cpe1_cp1_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "uimm19", HW_H_UIMM19, CGEN_MODE_UINT, OP_ENT (UIMM19), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_cpld_cp1_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_cpldi_cp1_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "slo12d", HW_H_SLO12, CGEN_MODE_INT, OP_ENT (SLO12D), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_cplw_cp1_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rb5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "si", HW_H_SI, CGEN_MODE_UINT, OP_ENT (SI), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_cplwi_cp1_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_ra5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "slo12w", HW_H_SLO12, CGEN_MODE_INT, OP_ENT (SLO12W), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_mfcpd_cp1_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "uimm12", HW_H_UIMM12, CGEN_MODE_UINT, OP_ENT (UIMM12), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ffb_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ffbi_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "uimm8_s", HW_H_UIMM8_S, CGEN_MODE_UINT, OP_ENT (UIMM8_S), 0, 0 },
  { OUTPUT, "rt5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RT5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_KADDW_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { INPUT, "ra5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RA5), 0, 0 },
  { INPUT, "rb5", HW_H_GR, CGEN_MODE_USI, OP_ENT (RB5), 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_RDOV_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "f_32_rt5", HW_H_UINT, CGEN_MODE_UINT, 0, 0, 0 },
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_CLROV_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ifcall9_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "disp9", HW_H_DISP9, CGEN_MODE_INT, OP_ENT (DISP9), 0, COND_REF },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ifcall_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "disp16", HW_H_DISP16, CGEN_MODE_INT, OP_ENT (DISP16), 0, COND_REF },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ifret_ops[] ATTRIBUTE_UNUSED = {
  { INPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, 0 },
  { OUTPUT, "pc", HW_H_PC, CGEN_MODE_USI, 0, 0, COND_REF },
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

static const CGEN_OPINST sfmt_ex5_it_ops[] ATTRIBUTE_UNUSED = {
  { END, (const char *)0, (enum cgen_hw_type)0, (enum cgen_mode)0, (enum cgen_operand_type)0, 0, 0 }
};

#undef OP_ENT
#undef INPUT
#undef OUTPUT
#undef END
#undef COND_REF

/* Operand instance lookup table.  */

static const CGEN_OPINST *nds32_cgen_opinst_table[MAX_INSNS] = {
  0,
  & sfmt_movi_ops[0],
  & sfmt_sethi_ops[0],
  & sfmt_addi_ops[0],
  & sfmt_add_ops[0],
  & sfmt_addi_ops[0],
  & sfmt_add_ops[0],
  & sfmt_addi_ops[0],
  & sfmt_add_ops[0],
  & sfmt_subri_ops[0],
  & sfmt_add_ops[0],
  & sfmt_andi_ops[0],
  & sfmt_and_ops[0],
  & sfmt_andi_ops[0],
  & sfmt_and_ops[0],
  & sfmt_andi_ops[0],
  & sfmt_and_ops[0],
  & sfmt_add_ops[0],
  & sfmt_add_ops[0],
  & sfmt_add_ops[0],
  & sfmt_seb_ops[0],
  & sfmt_seb_ops[0],
  & sfmt_seb_ops[0],
  & sfmt_seb_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_add_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_add_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_add_ops[0],
  & sfmt_srli_ops[0],
  & sfmt_add_ops[0],
  & sfmt_add_ops[0],
  & sfmt_mults64_ops[0],
  & sfmt_mults64_ops[0],
  & sfmt_madds64_ops[0],
  & sfmt_madds64_ops[0],
  & sfmt_madds64_ops[0],
  & sfmt_madds64_ops[0],
  & sfmt_mult32_ops[0],
  & sfmt_madd32_ops[0],
  & sfmt_madd32_ops[0],
  & sfmt_mfusr_ops[0],
  & sfmt_mtusr_ops[0],
  & sfmt_lbi_ops[0],
  & sfmt_lbi_bi_ops[0],
  & sfmt_lb_ops[0],
  & sfmt_lb_bi_ops[0],
  & sfmt_lhi_ops[0],
  & sfmt_lhi_bi_ops[0],
  & sfmt_lh_ops[0],
  & sfmt_lh_bi_ops[0],
  & sfmt_lwi_ops[0],
  & sfmt_lwi_bi_ops[0],
  & sfmt_lw_ops[0],
  & sfmt_lw_bi_ops[0],
  & sfmt_lw_ops[0],
  & sfmt_swup_ops[0],
  & sfmt_lbsi_ops[0],
  & sfmt_lbsi_bi_ops[0],
  & sfmt_lbs_ops[0],
  & sfmt_lbs_bi_ops[0],
  & sfmt_lhsi_ops[0],
  & sfmt_lhsi_bi_ops[0],
  & sfmt_lhs_ops[0],
  & sfmt_lhs_bi_ops[0],
  & sfmt_sbi_ops[0],
  & sfmt_sbi_bi_ops[0],
  & sfmt_sb_ops[0],
  & sfmt_sb_bi_ops[0],
  & sfmt_shi_ops[0],
  & sfmt_shi_bi_ops[0],
  & sfmt_sh_ops[0],
  & sfmt_sh_bi_ops[0],
  & sfmt_swi_ops[0],
  & sfmt_swi_bi_ops[0],
  & sfmt_sw_ops[0],
  & sfmt_sw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_llw_ops[0],
  & sfmt_scw_ops[0],
  & sfmt_j_ops[0],
  & sfmt_j_ops[0],
  & sfmt_jr_ops[0],
  & sfmt_ret_ops[0],
  & sfmt_jr_itoff_ops[0],
  & sfmt_jr_itoff_ops[0],
  & sfmt_jr_itoff_ops[0],
  & sfmt_jr_itoff_ops[0],
  & sfmt_jral_ops[0],
  & sfmt_jral_iton_ops[0],
  & sfmt_jral_iton_ops[0],
  & sfmt_beq_ops[0],
  & sfmt_beq_ops[0],
  & sfmt_beqz_ops[0],
  & sfmt_beqz_ops[0],
  & sfmt_beqz_ops[0],
  & sfmt_beqz_ops[0],
  & sfmt_beqz_ops[0],
  & sfmt_beqz_ops[0],
  & sfmt_beqz_ops[0],
  & sfmt_beqz_ops[0],
  & sfmt_mfsr_ops[0],
  & sfmt_mtsr_ops[0],
  & sfmt_setend_l_ops[0],
  & sfmt_setend_l_ops[0],
  & sfmt_setend_l_ops[0],
  & sfmt_setend_l_ops[0],
  & sfmt_cmovz_ops[0],
  & sfmt_cmovz_ops[0],
  & sfmt_dprefi_d_ops[0],
  & sfmt_dprefi_w_ops[0],
  & sfmt_dpref_ops[0],
  & sfmt_isync_ops[0],
  & sfmt_msync_ops[0],
  & sfmt_isb_ops[0],
  & sfmt_dsb_ops[0],
  & sfmt_standby_ops[0],
  & sfmt_trap_ops[0],
  & sfmt_teqz_ops[0],
  & sfmt_teqz_ops[0],
  & sfmt_trap_ops[0],
  & sfmt_trap_ops[0],
  & sfmt_isb_ops[0],
  & sfmt_tlbop_ops[0],
  & sfmt_cctl_ops[0],
  & sfmt_mults64_ops[0],
  & sfmt_mults64_ops[0],
  & sfmt_abs_ops[0],
  & sfmt_ave_ops[0],
  & sfmt_min_ops[0],
  & sfmt_min_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_slli_ops[0],
  & sfmt_seb_ops[0],
  & sfmt_clo_ops[0],
  & sfmt_bse_ops[0],
  & sfmt_bse_ops[0],
  & sfmt_pbsad_ops[0],
  & sfmt_pbsada_ops[0],
  & sfmt_mov55_ops[0],
  & sfmt_movi55_ops[0],
  & sfmt_addi45_ops[0],
  & sfmt_add45_ops[0],
  & sfmt_addi45_ops[0],
  & sfmt_add45_ops[0],
  & sfmt_srai45_ops[0],
  & sfmt_srli45_ops[0],
  & sfmt_slli333_ops[0],
  & sfmt_seb33_ops[0],
  & sfmt_seb33_ops[0],
  & sfmt_seb33_ops[0],
  & sfmt_seb33_ops[0],
  & sfmt_seb33_ops[0],
  & sfmt_seb33_ops[0],
  & sfmt_slli333_ops[0],
  & sfmt_add333_ops[0],
  & sfmt_slli333_ops[0],
  & sfmt_add333_ops[0],
  & sfmt_lwi333_ops[0],
  & sfmt_lwi333_bi_ops[0],
  & sfmt_lhi333_ops[0],
  & sfmt_lbi333_ops[0],
  & sfmt_swi333_ops[0],
  & sfmt_swi333_bi_ops[0],
  & sfmt_shi333_ops[0],
  & sfmt_sbi333_ops[0],
  & sfmt_lwi450_ops[0],
  & sfmt_swi450_ops[0],
  & sfmt_lwi37_ops[0],
  & sfmt_swi37_ops[0],
  & sfmt_beqz38_ops[0],
  & sfmt_beqz38_ops[0],
  & sfmt_beqs38_ops[0],
  & sfmt_beqs38_ops[0],
  & sfmt_j8_ops[0],
  & sfmt_jr5_ops[0],
  & sfmt_jr5_ops[0],
  & sfmt_jr5_ops[0],
  & sfmt_slti45_ops[0],
  & sfmt_slti45_ops[0],
  & sfmt_slt45_ops[0],
  & sfmt_slt45_ops[0],
  & sfmt_beqzs8_ops[0],
  & sfmt_beqzs8_ops[0],
  & sfmt_break16_ops[0],
  & sfmt_addi10_sp_ops[0],
  & sfmt_lwi37_sp_ops[0],
  & sfmt_swi37_sp_ops[0],
  & sfmt_bmski33_ops[0],
  & sfmt_bmski33_ops[0],
  & sfmt_addri36_sp_ops[0],
  & sfmt_lwi45_fe_ops[0],
  & sfmt_seb33_ops[0],
  & sfmt_seb33_ops[0],
  & sfmt_mul33_ops[0],
  & sfmt_mul33_ops[0],
  & sfmt_mul33_ops[0],
  & sfmt_mul33_ops[0],
  & sfmt_movpi45_ops[0],
  & sfmt_push25_ops[0],
  & sfmt_pop25_ops[0],
  & sfmt_movd44_ops[0],
  & sfmt_add5_pc_ops[0],
  & sfmt_break16v3_ops[0],
  & sfmt_addi_gp_ops[0],
  & sfmt_maddr32_ops[0],
  & sfmt_maddr32_ops[0],
  & sfmt_mulr64_ops[0],
  & sfmt_mulr64_ops[0],
  & sfmt_sbi_gp_ops[0],
  & sfmt_shi_gp_ops[0],
  & sfmt_swi_gp_ops[0],
  & sfmt_lbi_gp_ops[0],
  & sfmt_lbi_gp_ops[0],
  & sfmt_lhi_gp_ops[0],
  & sfmt_lhsi_gp_ops[0],
  & sfmt_lwi_gp_ops[0],
  & sfmt_divr_ops[0],
  & sfmt_divr_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lb_ops[0],
  & sfmt_sbup_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_lmw_bi_ops[0],
  & sfmt_beqc_ops[0],
  & sfmt_beqc_ops[0],
  & sfmt_jralnez_ops[0],
  & sfmt_jrnez_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_slli_ops[0],
  & sfmt_add_ops[0],
  & sfmt_bitci_ops[0],
  & sfmt_aaddl_ops[0],
  & sfmt_aaddl_ops[0],
  & sfmt_ala_ops[0],
  & sfmt_alr_ops[0],
  & sfmt_alr2_ops[0],
  & sfmt_asa_ops[0],
  & sfmt_asr_ops[0],
  & sfmt_aupi_ops[0],
  & sfmt_amfar_ops[0],
  & sfmt_amtar_ops[0],
  & sfmt_amtari_ops[0],
  & sfmt_asats48_ops[0],
  & sfmt_awext_ops[0],
  & sfmt_amadd_ops[0],
  & sfmt_amaddl_s_ops[0],
  & sfmt_amaddl2_s_ops[0],
  & sfmt_amaddl_l_ops[0],
  & sfmt_amaddl2_l_ops[0],
  & sfmt_amaddsa_ops[0],
  & sfmt_amadd_ops[0],
  & sfmt_amaddl_s_ops[0],
  & sfmt_amaddl2_s_ops[0],
  & sfmt_amaddl_l_ops[0],
  & sfmt_amaddl2_l_ops[0],
  & sfmt_amaddsa_ops[0],
  & sfmt_amadd_ops[0],
  & sfmt_amaddl_s_ops[0],
  & sfmt_amaddl2_s_ops[0],
  & sfmt_amaddl_l_ops[0],
  & sfmt_amaddl2_l_ops[0],
  & sfmt_amaddsa_ops[0],
  & sfmt_amadd_ops[0],
  & sfmt_amaddl_s_ops[0],
  & sfmt_amaddl2_s_ops[0],
  & sfmt_amaddl_l_ops[0],
  & sfmt_amaddl2_l_ops[0],
  & sfmt_amaddsa_ops[0],
  & sfmt_amnegs_ops[0],
  & sfmt_amnegsl_s_ops[0],
  & sfmt_amnegsl2_s_ops[0],
  & sfmt_amnegsl_l_ops[0],
  & sfmt_amnegsl2_l_ops[0],
  & sfmt_amnegssa_ops[0],
  & sfmt_amnegs_ops[0],
  & sfmt_amnegsl_s_ops[0],
  & sfmt_amnegsl2_s_ops[0],
  & sfmt_amnegsl_l_ops[0],
  & sfmt_amnegsl2_l_ops[0],
  & sfmt_amnegssa_ops[0],
  & sfmt_amnegs_ops[0],
  & sfmt_amnegsl_s_ops[0],
  & sfmt_amnegsl2_s_ops[0],
  & sfmt_amnegsl_l_ops[0],
  & sfmt_amnegsl2_l_ops[0],
  & sfmt_amnegssa_ops[0],
  & sfmt_azol_ops[0],
  & sfmt_amabbs_ops[0],
  & sfmt_amabts_ops[0],
  & sfmt_amatbs_ops[0],
  & sfmt_amatts_ops[0],
  & sfmt_ambbs_ops[0],
  & sfmt_ambts_ops[0],
  & sfmt_amtbs_ops[0],
  & sfmt_amtts_ops[0],
  & sfmt_amabbsl_s_ops[0],
  & sfmt_amabbsl_l_ops[0],
  & sfmt_amabbsl2_s_ops[0],
  & sfmt_amabbsl2_l_ops[0],
  & sfmt_amabbssa_ops[0],
  & sfmt_amabtsl_s_ops[0],
  & sfmt_amabtsl_l_ops[0],
  & sfmt_amabtsl2_s_ops[0],
  & sfmt_amabtsl2_l_ops[0],
  & sfmt_amabtssa_ops[0],
  & sfmt_amatbsl_s_ops[0],
  & sfmt_amatbsl_l_ops[0],
  & sfmt_amatbsl2_s_ops[0],
  & sfmt_amatbsl2_l_ops[0],
  & sfmt_amatbssa_ops[0],
  & sfmt_amattsl_s_ops[0],
  & sfmt_amattsl_l_ops[0],
  & sfmt_amattsl2_s_ops[0],
  & sfmt_amattsl2_l_ops[0],
  & sfmt_amattssa_ops[0],
  & sfmt_ambbsl_s_ops[0],
  & sfmt_ambbsl_l_ops[0],
  & sfmt_ambbsl2_s_ops[0],
  & sfmt_ambbsl2_l_ops[0],
  & sfmt_ambbssa_ops[0],
  & sfmt_ambtsl_s_ops[0],
  & sfmt_ambtsl_l_ops[0],
  & sfmt_ambtsl2_s_ops[0],
  & sfmt_ambtsl2_l_ops[0],
  & sfmt_ambtssa_ops[0],
  & sfmt_amtbsl_s_ops[0],
  & sfmt_amtbsl_l_ops[0],
  & sfmt_amtbsl2_s_ops[0],
  & sfmt_amtbsl2_l_ops[0],
  & sfmt_amtbssa_ops[0],
  & sfmt_amttsl_s_ops[0],
  & sfmt_amttsl_l_ops[0],
  & sfmt_amttsl2_s_ops[0],
  & sfmt_amttsl2_l_ops[0],
  & sfmt_amttssa_ops[0],
  & sfmt_amawbs_ops[0],
  & sfmt_amawts_ops[0],
  & sfmt_amwbs_ops[0],
  & sfmt_amwts_ops[0],
  & sfmt_amawbsl_s_ops[0],
  & sfmt_amawbsl_l_ops[0],
  & sfmt_amawbsl2_s_ops[0],
  & sfmt_amawbsl2_l_ops[0],
  & sfmt_amawbssa_ops[0],
  & sfmt_amawtsl_s_ops[0],
  & sfmt_amawtsl_l_ops[0],
  & sfmt_amawtsl2_s_ops[0],
  & sfmt_amawtsl2_l_ops[0],
  & sfmt_amawtssa_ops[0],
  & sfmt_amwbsl_s_ops[0],
  & sfmt_amwbsl_l_ops[0],
  & sfmt_amwbsl2_s_ops[0],
  & sfmt_amwbsl2_l_ops[0],
  & sfmt_amwbssa_ops[0],
  & sfmt_amwtsl_s_ops[0],
  & sfmt_amwtsl_l_ops[0],
  & sfmt_amwtsl2_s_ops[0],
  & sfmt_amwtsl2_l_ops[0],
  & sfmt_amwtssa_ops[0],
  & sfmt_amfar2_ops[0],
  & sfmt_amtar2_ops[0],
  & sfmt_fls_ops[0],
  & sfmt_fls_ops[0],
  & sfmt_flsi_ops[0],
  & sfmt_flsi_ops[0],
  & sfmt_fmfcfg_ops[0],
  & sfmt_fmfcfg_ops[0],
  & sfmt_fmfcfg_ops[0],
  & sfmt_fmfsr_ops[0],
  & sfmt_fmfsr_ops[0],
  & sfmt_fls_ops[0],
  & sfmt_fls_ops[0],
  & sfmt_flsi_ops[0],
  & sfmt_flsi_ops[0],
  & sfmt_fs2d_ops[0],
  & sfmt_fabss_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fabss_ops[0],
  & sfmt_fabss_ops[0],
  & sfmt_fabss_ops[0],
  & sfmt_fabss_ops[0],
  & sfmt_fabss_ops[0],
  & sfmt_fabss_ops[0],
  & sfmt_fadds_ops[0],
  & sfmt_fabss_ops[0],
  & sfmt_fabsd_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_fcmovnd_ops[0],
  & sfmt_fcmovnd_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_fcmpeqs_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_fd2s_ops[0],
  & sfmt_fd2s_ops[0],
  & sfmt_fd2s_ops[0],
  & sfmt_fd2s_ops[0],
  & sfmt_fd2s_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_fld_ops[0],
  & sfmt_fld_ops[0],
  & sfmt_fldi_ops[0],
  & sfmt_fldi_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_fmfdr_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_fmfdr_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_fld_ops[0],
  & sfmt_fld_ops[0],
  & sfmt_fldi_ops[0],
  & sfmt_fldi_ops[0],
  & sfmt_fs2d_ops[0],
  & sfmt_fs2d_ops[0],
  & sfmt_faddd_ops[0],
  & sfmt_fs2d_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpe1_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpld_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cpldi_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplw_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_cplwi_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_mfcpd_cp1_ops[0],
  & sfmt_ffb_ops[0],
  & sfmt_ffbi_ops[0],
  & sfmt_ffb_ops[0],
  & sfmt_ffb_ops[0],
  & sfmt_ffb_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_KADDW_ops[0],
  & sfmt_RDOV_ops[0],
  & sfmt_CLROV_ops[0],
  & sfmt_ifcall9_ops[0],
  & sfmt_ifcall_ops[0],
  & sfmt_ifret_ops[0],
  & sfmt_ex5_it_ops[0],
  & sfmt_ex5_it_ops[0],
};

/* Function to call before using the operand instance table.  */

void
nds32_cgen_init_opinst_table (cd)
     CGEN_CPU_DESC cd;
{
  int i;
  const CGEN_OPINST **oi = & nds32_cgen_opinst_table[0];
  CGEN_INSN *insns = (CGEN_INSN *) cd->insn_table.init_entries;
  for (i = 0; i < MAX_INSNS; ++i)
    insns[i].opinst = oi[i];
}
