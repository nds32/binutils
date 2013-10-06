/* Instruction opcode table for nds32.

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
#include "libiberty.h"

/* -- opc.c */
/* We need to hash the instructions properly to disassemble. The way it works
   is to hash the 32-bit instructions to one half of the hash table and 16-bit
   instructions to the other half of the hash table.  */

unsigned int
nds32_cgen_dis_hash (const char *buffer, CGEN_INSN_INT value)
{
  /* Handles 32-bit and 16-bit instructions differently.  */
  if ((buffer[0] & 0x80) == (IFMT_32 << 7))
    /* 7 MSBs for 32-bit instructions.  */
    return (value >> 25) & 0x7f;
  else
    /* 5 MSBs for 16-bit instructions.  */
    return (value >> 9) & 0x7c;
}

/* Special check to ensure that instruction exists for given machine.  */

int
nds32_cgen_insn_supported (CGEN_CPU_DESC cd, const CGEN_INSN *insn)
{
  int machs = CGEN_INSN_ATTR_VALUE (insn, CGEN_INSN_MACH);

  /* If attributes are absent, assume no restriction.  */
  if (machs == 0)
    machs = ~0;

  return (machs & cd->machs);
}

/* -- asm.c */
/* The hash functions are recorded here to help keep assembler code out of
   the disassembler and vice versa.  */

static int asm_hash_insn_p        (const CGEN_INSN *);
static unsigned int asm_hash_insn (const char *);
static int dis_hash_insn_p        (const CGEN_INSN *);
static unsigned int dis_hash_insn (const char *, CGEN_INSN_INT);

/* Instruction formats.  */

#define F(f) & nds32_cgen_ifld_table[NDS32_##f]
static const CGEN_IFMT ifmt_empty ATTRIBUTE_UNUSED = {
  0, 0, 0x0, { { 0 } }
};

static const CGEN_IFMT ifmt_movi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SLO20) }, { 0 } }
};

static const CGEN_IFMT ifmt_sethi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_UHI20) }, { 0 } }
};

static const CGEN_IFMT ifmt_addi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_ULO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_add ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_subri ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_seb ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_slli ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T3_UIMM5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_mults64 ATTRIBUTE_UNUSED = {
  32, 32, 0xffd003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RD24) }, { F (F_32_RD1) }, { F (F_32_RD20) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_mfusr ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_USR) }, { F (F_32_GROUP) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lb ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe00003f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_j ATTRIBUTE_UNUSED = {
  32, 32, 0xff000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T0_DISP24) }, { 0 } }
};

static const CGEN_IFMT ifmt_jr ATTRIBUTE_UNUSED = {
  32, 32, 0xffff83ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32T3_RES10_7) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_jral ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f83ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_beq ATTRIBUTE_UNUSED = {
  32, 32, 0xfe004000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SUB1) }, { F (F_32T2_DISP14) }, { 0 } }
};

static const CGEN_IFMT ifmt_beqz ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_mfsr ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_SR10) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_setend_l ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_SR10) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_dprefi_d ATTRIBUTE_UNUSED = {
  32, 32, 0xff000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T2_ST4) }, { F (F_32_RA5) }, { F (F_32T2_SLO15D) }, { 0 } }
};

static const CGEN_IFMT ifmt_dprefi_w ATTRIBUTE_UNUSED = {
  32, 32, 0xff000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T2_ST4) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_dpref ATTRIBUTE_UNUSED = {
  32, 32, 0xff0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T2_ST4) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_isync ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0fffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_SR10) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_msync ATTRIBUTE_UNUSED = {
  32, 32, 0xffffff1f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_RES12_12) }, { F (F_32T3_EXT3) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_isb ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_SWID15) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_standby ATTRIBUTE_UNUSED = {
  32, 32, 0xffffff9f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_SR10) }, { F (F_32T4_RES3_22) }, { F (F_32T4_EXT2) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_trap ATTRIBUTE_UNUSED = {
  32, 32, 0xfff0001f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_SWID15) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_teqz ATTRIBUTE_UNUSED = {
  32, 32, 0xfe00001f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_SWID15) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_tlbop ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007c1f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_cctl ATTRIBUTE_UNUSED = {
  32, 32, 0xfe00781f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_4_17) }, { F (F_32TX_1_21) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_pbsad ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_mov55 ATTRIBUTE_UNUSED = {
  16, 16, 0xfc00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC141) }, { F (F_16_RT5H) }, { F (F_16_RA5H) }, { 0 } }
};

static const CGEN_IFMT ifmt_movi55 ATTRIBUTE_UNUSED = {
  16, 16, 0xfc00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC141) }, { F (F_16_RT5H) }, { F (F_16_SIMM5) }, { 0 } }
};

static const CGEN_IFMT ifmt_addi45 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT4) }, { F (F_16_UIMM5) }, { 0 } }
};

static const CGEN_IFMT ifmt_add45 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT4) }, { F (F_16_RB5H) }, { 0 } }
};

static const CGEN_IFMT ifmt_srai45 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT4) }, { F (F_16_UIMM5) }, { 0 } }
};

static const CGEN_IFMT ifmt_slli333 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_UIMM3) }, { 0 } }
};

static const CGEN_IFMT ifmt_seb33 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe07, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_OPC143323) }, { 0 } }
};

static const CGEN_IFMT ifmt_add333 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_RB3) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi333 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3W) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhi333 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbi333 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi450 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT4) }, { F (F_16_RA5H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi37 ATTRIBUTE_UNUSED = {
  16, 16, 0xf880, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_RT3) }, { F (F_16_OPC1431) }, { F (F_16_ULO7W) }, { 0 } }
};

static const CGEN_IFMT ifmt_beqz38 ATTRIBUTE_UNUSED = {
  16, 16, 0xf800, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_RT3) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_j8 ATTRIBUTE_UNUSED = {
  16, 16, 0xff00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_jr5 ATTRIBUTE_UNUSED = {
  16, 16, 0xffe0, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_OPC1433) }, { F (F_16_RB5H) }, { 0 } }
};

static const CGEN_IFMT ifmt_break16 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_SWID9) }, { 0 } }
};

static const CGEN_IFMT ifmt_addi10_sp ATTRIBUTE_UNUSED = {
  16, 16, 0xfc00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC141) }, { F (F_16_SIMM10) }, { 0 } }
};

static const CGEN_IFMT ifmt_bmski33 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe07, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_UIMM3_10) }, { F (F_16_OPC143323) }, { 0 } }
};

static const CGEN_IFMT ifmt_addri36_sp ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_UIMM6W) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi45_fe ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT4) }, { F (F_16_SIMM5W) }, { 0 } }
};

static const CGEN_IFMT ifmt_movpi45 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT4) }, { F (F_16_SUIMM5) }, { 0 } }
};

static const CGEN_IFMT ifmt_push25 ATTRIBUTE_UNUSED = {
  16, 16, 0xff80, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_OPC1431) }, { F (F_16_MASK2) }, { F (F_16_UIMM5D) }, { 0 } }
};

static const CGEN_IFMT ifmt_movd44 ATTRIBUTE_UNUSED = {
  16, 16, 0xff00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_RT5E) }, { F (F_16_RA5E) }, { 0 } }
};

static const CGEN_IFMT ifmt_break16v3 ATTRIBUTE_UNUSED = {
  16, 16, 0xffe0, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_OPC1433) }, { F (F_16_SWID5) }, { 0 } }
};

static const CGEN_IFMT ifmt_addi_gp ATTRIBUTE_UNUSED = {
  32, 32, 0xfe080000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32V2_19_1) }, { F (F_32_SLO19) }, { 0 } }
};

static const CGEN_IFMT ifmt_shi_gp ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0c0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32V2_19_2) }, { F (F_32_SLO18H) }, { 0 } }
};

static const CGEN_IFMT ifmt_swi_gp ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0e0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32V2_19_2) }, { F (F_32V2_17_1) }, { F (F_32_SLO17W) }, { 0 } }
};

static const CGEN_IFMT ifmt_divr ATTRIBUTE_UNUSED = {
  32, 32, 0xfe00001f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32_RS5) }, { F (F_32T3_SUB10G2) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_beqc ATTRIBUTE_UNUSED = {
  32, 32, 0xfe080000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T21_SUB1) }, { F (F_32T2_SIMM11) }, { F (F_32T1_DISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_add_slli ATTRIBUTE_UNUSED = {
  32, 32, 0xfe00001f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T21_ULO5) }, { F (F_32T21_SUBOP) }, { 0 } }
};

static const CGEN_IFMT ifmt_aaddl ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00020, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_RC4_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_ala ATTRIBUTE_UNUSED = {
  32, 32, 0xfffe7fe0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RES3_19_A) }, { F (F_32_DH2_16_A) }, { F (F_32_RES5_14_A) }, { F (F_32_RES1_9_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_alr ATTRIBUTE_UNUSED = {
  32, 32, 0xfff07fe0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RA5_A) }, { F (F_32_RES5_14_A) }, { F (F_32_RES1_9_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_alr2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfff003c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5P_A) }, { F (F_32_RES1_9_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_aupi ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffe0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RES3_19_A) }, { F (F_32_RES2_16_A) }, { F (F_32_RES5_14_A) }, { F (F_32_RES1_9_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amfar ATTRIBUTE_UNUSED = {
  32, 32, 0xfff07fe0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RD5_A) }, { F (F_32_RES5_14_A) }, { F (F_32_RES1_9_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_ARIDX5_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amtar ATTRIBUTE_UNUSED = {
  32, 32, 0xfff07fe0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RA5_A) }, { F (F_32_RES5_14_A) }, { F (F_32_RES1_9_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_ARIDX5_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amtari ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_ARIDX4_A) }, { F (F_32_IMM16_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_asats48 ATTRIBUTE_UNUSED = {
  32, 32, 0xfffffdff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RES3_19_A) }, { F (F_32_RES2_16_A) }, { F (F_32_RES5_14_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_awext ATTRIBUTE_UNUSED = {
  32, 32, 0xfff07de0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RD5_A) }, { F (F_32_RES5_14_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_LSBLOC_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amadd ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amaddl_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001e0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amaddl2_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5P_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amaddl_l ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA4_19_A) }, { F (F_32_C1_15_A) }, { F (F_32_RB3_14_A) }, { F (F_32_RC2_11_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_RC1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amaddl2_l ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA4_19_A) }, { F (F_32_C1_15_A) }, { F (F_32_RB3_14_A) }, { F (F_32_RC2_11_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amaddsa ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00180, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP2_8_A) }, { F (F_32_DH2_6_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_azol ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RES3_19_A) }, { F (F_32_RES2_16_A) }, { F (F_32_RES5_14_A) }, { F (F_32_RES1_9_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amabbs ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amabts ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amatbs ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amatts ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amabbsl_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001e0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amabbsl2_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5P_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amabbssa ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00180, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP2_8_A) }, { F (F_32_DH2_6_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amabtsl_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001e0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amabtsl2_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5P_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amabtssa ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00180, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP2_8_A) }, { F (F_32_DH2_6_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amatbsl_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001e0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amatbsl2_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5P_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amatbssa ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00180, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP2_8_A) }, { F (F_32_DH2_6_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amattsl_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001e0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amattsl2_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5P_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amattssa ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00180, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP2_8_A) }, { F (F_32_DH2_6_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amawbs ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amawts ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_RES5_4_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amawbsl_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001e0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amawbsl2_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5P_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amawbssa ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00180, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP2_8_A) }, { F (F_32_DH2_6_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amawtsl_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001e0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amawtsl2_s ATTRIBUTE_UNUSED = {
  32, 32, 0xfff001c0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5P_A) }, { F (F_32_D1_A) }, { F (F_32_OP3_8_A) }, { F (F_32_M2_5_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amawtssa ATTRIBUTE_UNUSED = {
  32, 32, 0xfff00180, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_AM_A) }, { F (F_32_RA5_A) }, { F (F_32_RB5_A) }, { F (F_32_D1_A) }, { F (F_32_OP2_8_A) }, { F (F_32_DH2_6_A) }, { F (F_32_IM1_4_A) }, { F (F_32_M2_3_A) }, { F (F_32_I2_1_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_amfar2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfff07fe0, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_OP2_24_A) }, { F (F_32_OP3_22_A) }, { F (F_32_RD5_A) }, { F (F_32_RES5_14_A) }, { F (F_32_RES1_9_A) }, { F (F_32_OP3_8_A) }, { F (F_32_OP1_5_A) }, { F (F_32_ARIDX5_A) }, { 0 } }
};

static const CGEN_IFMT ifmt_fls ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_flsi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_fmfcfg ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0fffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_5_17) }, { F (F_32TX_4_22) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fmfsr ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32TX_4_22) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fs2d ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_3_17) }, { F (F_32TX_2_20) }, { F (F_32TX_2_22) }, { F (F_32TX_2_24) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fabss ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_3_17) }, { F (F_32TX_2_20) }, { F (F_32TX_2_22) }, { F (F_32TX_2_24) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fadds ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32TX_2_22) }, { F (F_32TX_2_24) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fcmpeqs ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32TX_3_22) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fabsd ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_3_17) }, { F (F_32TX_2_20) }, { F (F_32TX_2_22) }, { F (F_32TX_2_24) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_faddd ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32TX_2_22) }, { F (F_32TX_2_24) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fcmovnd ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32TX_2_22) }, { F (F_32TX_2_24) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fd2s ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_3_17) }, { F (F_32TX_2_20) }, { F (F_32TX_2_22) }, { F (F_32TX_2_24) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fld ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fldi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_fmfdr ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32TX_4_22) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpe1_cp1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe00003f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_19_7) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpldi_cp1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplwi_cp1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_mfcpd_cp1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_12_12) }, { F (F_32TX_2_24) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_ffb ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T4_RES3_22) }, { F (F_32_OP1_S) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_ffbi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe00007f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_UIMM8_S) }, { F (F_32_OP1_S) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_RDOV ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0fffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_ifcall9 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_32T1_DISP9) }, { 0 } }
};

static const CGEN_IFMT ifmt_ifcall ATTRIBUTE_UNUSED = {
  32, 32, 0xffff0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_ifret ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32T3_RES10_7) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

#undef F

#define A(a) (1 << CGEN_INSN_##a)
#define OPERAND(op) NDS32_OPERAND_##op
#define MNEM CGEN_SYNTAX_MNEMONIC /* syntax value for mnemonic */
#define OP(field) CGEN_SYNTAX_MAKE_FIELD (OPERAND (field))

/* The instruction table.  */

static const CGEN_OPCODE nds32_cgen_insn_opcode_table[MAX_INSNS] =
{
  /* Special null first entry.
     A `num' value of zero is thus invalid.
     Also, the special `invalid' insn resides here.  */
  { { 0, 0, 0, 0 }, {{0}}, 0, {0}},
/* movi $rt5,$slo20 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (SLO20), 0 } },
    & ifmt_movi, { 0x44000000 }
  },
/* sethi $rt5,$uhi20 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (UHI20), 0 } },
    & ifmt_sethi, { 0x46000000 }
  },
/* addi $rt5,$ra5,$slo15 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (SLO15), 0 } },
    & ifmt_addi, { 0x50000000 }
  },
/* add $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000000 }
  },
/* sltsi $rt5,$ra5,$slo15 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (SLO15), 0 } },
    & ifmt_addi, { 0x5e000000 }
  },
/* slts $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000007 }
  },
/* slti $rt5,$ra5,$slo15 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (SLO15), 0 } },
    & ifmt_addi, { 0x5c000000 }
  },
/* slt $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000006 }
  },
/* subri $rt5,$ra5,$slo15 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (SLO15), 0 } },
    & ifmt_subri, { 0x52000000 }
  },
/* sub $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000001 }
  },
/* andi $rt5,$ra5,$ulo15 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (ULO15), 0 } },
    & ifmt_addi, { 0x54000000 }
  },
/* and $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000002 }
  },
/* xori $rt5,$ra5,$ulo15 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (ULO15), 0 } },
    & ifmt_addi, { 0x56000000 }
  },
/* xor $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000003 }
  },
/* ori $rt5,$ra5,$ulo15 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (ULO15), 0 } },
    & ifmt_addi, { 0x58000000 }
  },
/* or $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000004 }
  },
/* nor $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000005 }
  },
/* sva $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000018 }
  },
/* svs $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000019 }
  },
/* seb $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_seb, { 0x40000010 }
  },
/* seh $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_seb, { 0x40000011 }
  },
/* zeh $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_seb, { 0x40000013 }
  },
/* wsbh $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_seb, { 0x40000014 }
  },
/* slli $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x40000008 }
  },
/* sll $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4000000c }
  },
/* srai $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x4000000a }
  },
/* sra $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4000000e }
  },
/* rotri $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x4000000b }
  },
/* rotr $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4000000f }
  },
/* srli $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x40000009 }
  },
/* srl $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4000000d }
  },
/* mul $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000024 }
  },
/* mults64 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x42000028 }
  },
/* mult64 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x42000029 }
  },
/* madds64 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x4200002a }
  },
/* madd64 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x4200002b }
  },
/* msubs64 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x4200002c }
  },
/* msub64 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x4200002d }
  },
/* mult32 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x42000031 }
  },
/* madd32 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x42000033 }
  },
/* msub32 $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x42000035 }
  },
/* mfusr $rt5,$mfusridx */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (MFUSRIDX), 0 } },
    & ifmt_mfusr, { 0x42000020 }
  },
/* mtusr $rt5,$mtusridx */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (MTUSRIDX), 0 } },
    & ifmt_mfusr, { 0x42000021 }
  },
/* lbi $rt5,[$ra5+$slo15b] */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (SLO15B), ']', 0 } },
    & ifmt_lbi, { 0x0 }
  },
/* lbi.bi $rt5,[$ra5],$slo15b */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15B), 0 } },
    & ifmt_lbi, { 0x8000000 }
  },
/* lb $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000000 }
  },
/* lb.bi $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb, { 0x38000004 }
  },
/* lhi $rt5,[$ra5+$slo15h] */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (SLO15H), ']', 0 } },
    & ifmt_lhi, { 0x2000000 }
  },
/* lhi.bi $rt5,[$ra5],$slo15h */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15H), 0 } },
    & ifmt_lhi, { 0xa000000 }
  },
/* lh $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000001 }
  },
/* lh.bi $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb, { 0x38000005 }
  },
/* lwi $rt5,[$ra5+$slo15w] */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (SLO15W), ']', 0 } },
    & ifmt_lwi, { 0x4000000 }
  },
/* lwi.bi $rt5,[$ra5],$slo15w */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15W), 0 } },
    & ifmt_lwi, { 0xc000000 }
  },
/* lw $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000002 }
  },
/* lw.bi $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb, { 0x38000006 }
  },
/* lwup $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000022 }
  },
/* swup $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x3800002a }
  },
/* lbsi $rt5,[$ra5+$slo15b] */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (SLO15B), ']', 0 } },
    & ifmt_lbi, { 0x20000000 }
  },
/* lbsi.bi $rt5,[$ra5],$slo15b */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15B), 0 } },
    & ifmt_lbi, { 0x28000000 }
  },
/* lbs $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000010 }
  },
/* lbs.bi $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb, { 0x38000014 }
  },
/* lhsi $rt5,[$ra5+$slo15h] */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (SLO15H), ']', 0 } },
    & ifmt_lhi, { 0x22000000 }
  },
/* lhsi.bi $rt5,[$ra5],$slo15h */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15H), 0 } },
    & ifmt_lhi, { 0x2a000000 }
  },
/* lhs $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000011 }
  },
/* lhs.bi $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb, { 0x38000015 }
  },
/* sbi $rt5,[$ra5+$slo15b] */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (SLO15B), ']', 0 } },
    & ifmt_lbi, { 0x10000000 }
  },
/* sbi.bi $rt5,[$ra5],$slo15b */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15B), 0 } },
    & ifmt_lbi, { 0x18000000 }
  },
/* sb $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000008 }
  },
/* sb.bi $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb, { 0x3800000c }
  },
/* shi $rt5,[$ra5+$slo15h] */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (SLO15H), ']', 0 } },
    & ifmt_lhi, { 0x12000000 }
  },
/* shi.bi $rt5,[$ra5],$slo15h */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15H), 0 } },
    & ifmt_lhi, { 0x1a000000 }
  },
/* sh $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000009 }
  },
/* sh.bi $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb, { 0x3800000d }
  },
/* swi $rt5,[$ra5+$slo15w] */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (SLO15W), ']', 0 } },
    & ifmt_lwi, { 0x14000000 }
  },
/* swi.bi $rt5,[$ra5],$slo15w */
  {
    { 0, 0, 0, 2 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15W), 0 } },
    & ifmt_lwi, { 0x1c000000 }
  },
/* sw $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x3800000a }
  },
/* sw.bi $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb, { 0x3800000e }
  },
/* lmw.bi $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000000 }
  },
/* lmw.bim $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000004 }
  },
/* lmw.bd $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000008 }
  },
/* lmw.bdm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a00000c }
  },
/* lmw.ai $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000010 }
  },
/* lmw.aim $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000014 }
  },
/* lmw.ad $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000018 }
  },
/* lmw.adm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a00001c }
  },
/* smw.bi $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000020 }
  },
/* smw.bim $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000024 }
  },
/* smw.bd $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000028 }
  },
/* smw.bdm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a00002c }
  },
/* smw.ai $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000030 }
  },
/* smw.aim $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000034 }
  },
/* smw.ad $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000038 }
  },
/* smw.adm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a00003c }
  },
/* llw $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000018 }
  },
/* scw $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000019 }
  },
/* j $disp24 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DISP24), 0 } },
    & ifmt_j, { 0x48000000 }
  },
/* jal $disp24 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DISP24), 0 } },
    & ifmt_j, { 0x49000000 }
  },
/* jr $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jr, { 0x4a000000 }
  },
/* ret $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jr, { 0x4a000020 }
  },
/* jr.itoff $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jr, { 0x4a000100 }
  },
/* jr.toff $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jr, { 0x4a000300 }
  },
/* ret.itoff $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jr, { 0x4a000120 }
  },
/* ret.toff $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jr, { 0x4a000320 }
  },
/* jral $rt5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RB5), 0 } },
    & ifmt_jral, { 0x4a000001 }
  },
/* jral.iton $rt5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RB5), 0 } },
    & ifmt_jral, { 0x4a000101 }
  },
/* jral.ton $rt5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RB5), 0 } },
    & ifmt_jral, { 0x4a000301 }
  },
/* beq $rt5,$ra5,$disp14 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (DISP14), 0 } },
    & ifmt_beq, { 0x4c000000 }
  },
/* bne $rt5,$ra5,$disp14 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (DISP14), 0 } },
    & ifmt_beq, { 0x4c004000 }
  },
/* beqz $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz, { 0x4e020000 }
  },
/* bnez $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz, { 0x4e030000 }
  },
/* bgez $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz, { 0x4e040000 }
  },
/* bltz $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz, { 0x4e050000 }
  },
/* bgtz $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz, { 0x4e060000 }
  },
/* blez $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz, { 0x4e070000 }
  },
/* bgezal $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz, { 0x4e0c0000 }
  },
/* bltzal $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz, { 0x4e0d0000 }
  },
/* mfsr $rt5,$sr10 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (SR10), 0 } },
    & ifmt_mfsr, { 0x64000002 }
  },
/* mtsr $rt5,$sr10 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (SR10), 0 } },
    & ifmt_mfsr, { 0x64000003 }
  },
/* setend.l */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_setend_l, { 0x64020023 }
  },
/* setend.b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_setend_l, { 0x64120023 }
  },
/* setgie.d */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_setend_l, { 0x64020043 }
  },
/* setgie.e */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_setend_l, { 0x64120043 }
  },
/* cmovz $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4000001a }
  },
/* cmovn $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4000001b }
  },
/* dprefi.d $dprefst,[$ra5+$slo15d] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DPREFST), ',', '[', OP (RA5), '+', OP (SLO15D), ']', 0 } },
    & ifmt_dprefi_d, { 0x27000000 }
  },
/* dprefi.w $dprefst,[$ra5+$slo15w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DPREFST), ',', '[', OP (RA5), '+', OP (SLO15W), ']', 0 } },
    & ifmt_dprefi_w, { 0x26000000 }
  },
/* dpref $dprefst,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DPREFST), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_dpref, { 0x38000013 }
  },
/* isync $rt5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), 0 } },
    & ifmt_isync, { 0x6400000d }
  },
/* msync $msyncst */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (MSYNCST), 0 } },
    & ifmt_msync, { 0x6400000c }
  },
/* isb */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_isb, { 0x64000009 }
  },
/* dsb */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_isb, { 0x64000008 }
  },
/* standby $standbyst */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (STANDBYST), 0 } },
    & ifmt_standby, { 0x64000000 }
  },
/* trap $swid15 */
  {
    { 0, 0, 0, 4 },
    { { MNEM, ' ', OP (SWID15), 0 } },
    & ifmt_trap, { 0x64000005 }
  },
/* teqz $rt5,$swid15 */
  {
    { 0, 0, 0, 5 },
    { { MNEM, ' ', OP (RT5), ',', OP (SWID15), 0 } },
    & ifmt_teqz, { 0x64000006 }
  },
/* tnez $rt5,$swid15 */
  {
    { 0, 0, 0, 5 },
    { { MNEM, ' ', OP (RT5), ',', OP (SWID15), 0 } },
    & ifmt_teqz, { 0x64000007 }
  },
/* break $swid15 */
  {
    { 0, 0, 0, 4 },
    { { MNEM, ' ', OP (SWID15), 0 } },
    & ifmt_trap, { 0x6400000a }
  },
/* syscall $swid15 */
  {
    { 0, 0, 0, 4 },
    { { MNEM, ' ', OP (SWID15), 0 } },
    & ifmt_trap, { 0x6400000b }
  },
/* iret */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_isb, { 0x64000004 }
  },
/* tlbop $rt5,$ra5,$tlbopst */
  {
    { 0, 0, 0, 6 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (TLBOPST), 0 } },
    & ifmt_tlbop, { 0x6400000e }
  },
/* cctl $rt5,$ra5,$cctlst,$cctllvl */
  {
    { 0, 0, 0, 7 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (CCTLST), ',', OP (CCTLLVL), 0 } },
    & ifmt_cctl, { 0x64000001 }
  },
/* divs $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x4200002e }
  },
/* div $rd1,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD1), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_mults64, { 0x4200002f }
  },
/* abs $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_seb, { 0x42000003 }
  },
/* ave $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000002 }
  },
/* min $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000001 }
  },
/* max $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000000 }
  },
/* bset $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x42000008 }
  },
/* btgl $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x4200000a }
  },
/* bclr $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x42000009 }
  },
/* btst $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x4200000b }
  },
/* clips $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x42000004 }
  },
/* clip $rt5,$ra5,$uimm5 */
  {
    { 0, 0, 0, 1 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM5), 0 } },
    & ifmt_slli, { 0x42000005 }
  },
/* clz $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_seb, { 0x42000007 }
  },
/* clo $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_seb, { 0x42000006 }
  },
/* bse $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4200000c }
  },
/* bsp $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4200000d }
  },
/* pbsad $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_pbsad, { 0x70000000 }
  },
/* pbsada $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_pbsad, { 0x70000001 }
  },
/* mov55 $rt5h,$ra5h */
  {
    { 1, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5H), ',', OP (RA5H), 0 } },
    & ifmt_mov55, { 0x8000 }
  },
/* movi55 $rt5h,$simm5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5H), ',', OP (SIMM5H), 0 } },
    & ifmt_movi55, { 0x8400 }
  },
/* addi45 $rt4,$imm5u */
  {
    { 0, 0, 0, 8 },
    { { MNEM, ' ', OP (RT4), ',', OP (IMM5U), 0 } },
    & ifmt_addi45, { 0x8c00 }
  },
/* add45 $rt4,$rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT4), ',', OP (RB5H), 0 } },
    & ifmt_add45, { 0x8800 }
  },
/* subi45 $rt4,$imm5u */
  {
    { 0, 0, 0, 8 },
    { { MNEM, ' ', OP (RT4), ',', OP (IMM5U), 0 } },
    & ifmt_addi45, { 0x8e00 }
  },
/* sub45 $rt4,$rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT4), ',', OP (RB5H), 0 } },
    & ifmt_add45, { 0x8a00 }
  },
/* srai45 $rt4,$uimm5h */
  {
    { 0, 0, 0, 9 },
    { { MNEM, ' ', OP (RT4), ',', OP (UIMM5H), 0 } },
    & ifmt_srai45, { 0x9000 }
  },
/* srli45 $rt4,$uimm5h */
  {
    { 0, 0, 0, 10 },
    { { MNEM, ' ', OP (RT4), ',', OP (UIMM5H), 0 } },
    & ifmt_srai45, { 0x9200 }
  },
/* slli333 $rt3_7,$ra3,$uimm3 */
  {
    { 0, 0, 0, 11 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), ',', OP (UIMM3), 0 } },
    & ifmt_slli333, { 0x9400 }
  },
/* seb33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0x9602 }
  },
/* seh33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0x9603 }
  },
/* zeb33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0x9600 }
  },
/* zeh33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0x9601 }
  },
/* xlsb33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0x9604 }
  },
/* x11b33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0x9605 }
  },
/* addi333 $rt3_7,$ra3,$uimm3 */
  {
    { 0, 0, 0, 12 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), ',', OP (UIMM3), 0 } },
    & ifmt_slli333, { 0x9c00 }
  },
/* add333 $rt3_7,$ra3,$rb3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), ',', OP (RB3), 0 } },
    & ifmt_add333, { 0x9800 }
  },
/* subi333 $rt3_7,$ra3,$uimm3 */
  {
    { 0, 0, 0, 12 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), ',', OP (UIMM3), 0 } },
    & ifmt_slli333, { 0x9e00 }
  },
/* sub333 $rt3_7,$ra3,$rb3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), ',', OP (RB3), 0 } },
    & ifmt_add333, { 0x9a00 }
  },
/* lwi333 $rt3_7,[$ra3+$ulo3w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), '+', OP (ULO3W), ']', 0 } },
    & ifmt_lwi333, { 0xa000 }
  },
/* lwi333.bi $rt3_7,[$ra3],$ulo3w */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), ']', ',', OP (ULO3W), 0 } },
    & ifmt_lwi333, { 0xa200 }
  },
/* lhi333 $rt3_7,[$ra3+$ulo3h] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), '+', OP (ULO3H), ']', 0 } },
    & ifmt_lhi333, { 0xa400 }
  },
/* lbi333 $rt3_7,[$ra3+$ulo3b] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), '+', OP (ULO3B), ']', 0 } },
    & ifmt_lbi333, { 0xa600 }
  },
/* swi333 $rt3_7,[$ra3+$ulo3w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), '+', OP (ULO3W), ']', 0 } },
    & ifmt_lwi333, { 0xa800 }
  },
/* swi333.bi $rt3_7,[$ra3],$ulo3w */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), ']', ',', OP (ULO3W), 0 } },
    & ifmt_lwi333, { 0xaa00 }
  },
/* shi333 $rt3_7,[$ra3+$ulo3h] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), '+', OP (ULO3H), ']', 0 } },
    & ifmt_lhi333, { 0xac00 }
  },
/* sbi333 $rt3_7,[$ra3+$ulo3b] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), '+', OP (ULO3B), ']', 0 } },
    & ifmt_lbi333, { 0xae00 }
  },
/* lwi450 $rt4,[$ra5h] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT4), ',', '[', OP (RA5H), ']', 0 } },
    & ifmt_lwi450, { 0xb400 }
  },
/* swi450 $rt4,[$ra5h] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT4), ',', '[', OP (RA5H), ']', 0 } },
    & ifmt_lwi450, { 0xb600 }
  },
/* lwi37 $rt3,[\$fp+$ulo7w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', '[', '$', 'f', 'p', '+', OP (ULO7W), ']', 0 } },
    & ifmt_lwi37, { 0xb800 }
  },
/* swi37 $rt3,[\$fp+$ulo7w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', '[', '$', 'f', 'p', '+', OP (ULO7W), ']', 0 } },
    & ifmt_lwi37, { 0xb880 }
  },
/* beqz38 $rt3,$hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', OP (HSDISP8), 0 } },
    & ifmt_beqz38, { 0xc000 }
  },
/* bnez38 $rt3,$hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', OP (HSDISP8), 0 } },
    & ifmt_beqz38, { 0xc800 }
  },
/* beqs38 $rt3,$hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', OP (HSDISP8), 0 } },
    & ifmt_beqz38, { 0xd000 }
  },
/* bnes38 $rt3,$hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', OP (HSDISP8), 0 } },
    & ifmt_beqz38, { 0xd800 }
  },
/* j8 $hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (HSDISP8), 0 } },
    & ifmt_j8, { 0xd500 }
  },
/* jr5 $rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5H), 0 } },
    & ifmt_jr5, { 0xdd00 }
  },
/* ret5 $rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5H), 0 } },
    & ifmt_jr5, { 0xdd80 }
  },
/* jral5 $rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5H), 0 } },
    & ifmt_jr5, { 0xdd20 }
  },
/* slti45 $rt4,$uimm5h */
  {
    { 0, 0, 0, 13 },
    { { MNEM, ' ', OP (RT4), ',', OP (UIMM5H), 0 } },
    & ifmt_srai45, { 0xe600 }
  },
/* sltsi45 $rt4,$uimm5h */
  {
    { 0, 0, 0, 14 },
    { { MNEM, ' ', OP (RT4), ',', OP (UIMM5H), 0 } },
    & ifmt_srai45, { 0xe400 }
  },
/* slt45 $rt4,$rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT4), ',', OP (RB5H), 0 } },
    & ifmt_add45, { 0xe200 }
  },
/* slts45 $rt4,$rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT4), ',', OP (RB5H), 0 } },
    & ifmt_add45, { 0xe000 }
  },
/* beqzs8 $hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (HSDISP8), 0 } },
    & ifmt_j8, { 0xe800 }
  },
/* bnezs8 $hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (HSDISP8), 0 } },
    & ifmt_j8, { 0xe900 }
  },
/* break16 $swid9 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (SWID9), 0 } },
    & ifmt_break16, { 0xea00 }
  },
/* addi10.sp $simm10 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (SIMM10), 0 } },
    & ifmt_addi10_sp, { 0xec00 }
  },
/* lwi37.sp $rt3,[+$ulo7w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', '[', '+', OP (ULO7W), ']', 0 } },
    & ifmt_lwi37, { 0xf000 }
  },
/* swi37.sp $rt3,[+$ulo7w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', '[', '+', OP (ULO7W), ']', 0 } },
    & ifmt_lwi37, { 0xf080 }
  },
/* bmski33 $rt3_7,$uimm3_10 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (UIMM3_10), 0 } },
    & ifmt_bmski33, { 0x9606 }
  },
/* fexti33 $rt3_7,$uimm3_10 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (UIMM3_10), 0 } },
    & ifmt_bmski33, { 0x9607 }
  },
/* addri36.sp $rt3_7,$uimm6w */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (UIMM6W), 0 } },
    & ifmt_addri36_sp, { 0xb000 }
  },
/* lwi45.fe $rt4,$simm5w */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT4), ',', OP (SIMM5W), 0 } },
    & ifmt_lwi45_fe, { 0xb200 }
  },
/* neg33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0xfe02 }
  },
/* not33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0xfe03 }
  },
/* mul33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0xfe04 }
  },
/* xor33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0xfe05 }
  },
/* and33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0xfe06 }
  },
/* or33 $rt3_7,$ra3 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', OP (RA3), 0 } },
    & ifmt_seb33, { 0xfe07 }
  },
/* movpi45 $rt4,$suimm5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT4), ',', OP (SUIMM5), 0 } },
    & ifmt_movpi45, { 0xfa00 }
  },
/* push25 $reglist,$uimm5d */
  {
    { 0, 0, 0, 15 },
    { { MNEM, ' ', OP (REGLIST), ',', OP (UIMM5D), 0 } },
    & ifmt_push25, { 0xfc00 }
  },
/* pop25 $reglist,$uimm5d */
  {
    { 0, 0, 0, 15 },
    { { MNEM, ' ', OP (REGLIST), ',', OP (UIMM5D), 0 } },
    & ifmt_push25, { 0xfc80 }
  },
/* movd44 $rt5e,$ra5e */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5E), ',', OP (RA5E), 0 } },
    & ifmt_movd44, { 0xfd00 }
  },
/* add5.pc $rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5H), 0 } },
    & ifmt_jr5, { 0xdda0 }
  },
/* break16 $swid5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (SWID5), 0 } },
    & ifmt_break16v3, { 0xea00 }
  },
/* addi.gp $rt5,$slo19 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (SLO19), 0 } },
    & ifmt_addi_gp, { 0x3e080000 }
  },
/* maddr32 $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000073 }
  },
/* msubr32 $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000075 }
  },
/* mulr64 $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000069 }
  },
/* mulsr64 $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000068 }
  },
/* sbi.gp $rt5,[+$slo19] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', '+', OP (SLO19), ']', 0 } },
    & ifmt_addi_gp, { 0x3e000000 }
  },
/* shi.gp $rt5,[+$slo18h] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', '+', OP (SLO18H), ']', 0 } },
    & ifmt_shi_gp, { 0x3c080000 }
  },
/* swi.gp $rt5,[+$slo17w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', '+', OP (SLO17W), ']', 0 } },
    & ifmt_swi_gp, { 0x3c0e0000 }
  },
/* lbi.gp $rt5,[+$slo19] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', '+', OP (SLO19), ']', 0 } },
    & ifmt_addi_gp, { 0x2e000000 }
  },
/* lbsi.gp $rt5,[+$slo19] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', '+', OP (SLO19), ']', 0 } },
    & ifmt_addi_gp, { 0x2e080000 }
  },
/* lhi.gp $rt5,[+$slo18h] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', '+', OP (SLO18H), ']', 0 } },
    & ifmt_shi_gp, { 0x3c000000 }
  },
/* lhsi.gp $rt5,[+$slo18h] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', '+', OP (SLO18H), ']', 0 } },
    & ifmt_shi_gp, { 0x3c040000 }
  },
/* lwi.gp $rt5,[+$slo17w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', '+', OP (SLO17W), ']', 0 } },
    & ifmt_swi_gp, { 0x3c0c0000 }
  },
/* divr $rt5,$rs5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RS5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_divr, { 0x40000017 }
  },
/* divsr $rt5,$rs5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RS5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_divr, { 0x40000016 }
  },
/* lmwa.bi $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000001 }
  },
/* lmwa.bim $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000005 }
  },
/* lmwa.bd $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000009 }
  },
/* lmwa.bdm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a00000d }
  },
/* lmwa.ai $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000011 }
  },
/* lmwa.aim $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000015 }
  },
/* lmwa.ad $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000019 }
  },
/* lmwa.adm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a00001d }
  },
/* smwa.bi $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000021 }
  },
/* smwa.bim $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000025 }
  },
/* smwa.bd $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000029 }
  },
/* smwa.bdm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a00002d }
  },
/* smwa.ai $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000031 }
  },
/* smwa.aim $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000035 }
  },
/* smwa.ad $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000039 }
  },
/* smwa.adm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a00003d }
  },
/* lbup $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000020 }
  },
/* sbup $rt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_lb, { 0x38000028 }
  },
/* lmwzb.b $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000002 }
  },
/* lmwzb.bm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000006 }
  },
/* lmwzb.a $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000012 }
  },
/* lmwzb.am $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000016 }
  },
/* smwzb.b $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000022 }
  },
/* smwzb.bm $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000026 }
  },
/* smwzb.a $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000032 }
  },
/* smwzb.am $rt5,[$ra5],$rb5,$mask4 */
  {
    { 0, 0, 0, 3 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), ',', OP (MASK4), 0 } },
    & ifmt_lmw_bi, { 0x3a000036 }
  },
/* beqc $rt5,$simm11,$disp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (SIMM11), ',', OP (DISP8), 0 } },
    & ifmt_beqc, { 0x5a000000 }
  },
/* bnec $rt5,$simm11,$disp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (SIMM11), ',', OP (DISP8), 0 } },
    & ifmt_beqc, { 0x5a080000 }
  },
/* jralnez $rt5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RB5), 0 } },
    & ifmt_jral, { 0x4a000003 }
  },
/* jrnez $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jr, { 0x4a000002 }
  },
/* add_slli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x40000000 }
  },
/* add_srli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x4000001c }
  },
/* sub_slli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x40000001 }
  },
/* sub_srli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x4000001d }
  },
/* and_slli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x40000002 }
  },
/* and_srli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x4000001e }
  },
/* or_slli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x40000004 }
  },
/* or_srli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x40000015 }
  },
/* xor_slli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x40000003 }
  },
/* xor_srli $rt5,$ra5,$rb5,$ulo5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), ',', OP (ULO5), 0 } },
    & ifmt_add_slli, { 0x4000001f }
  },
/* bitc $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x40000012 }
  },
/* bitci $rt5,$ra5,$ulo15 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (ULO15), 0 } },
    & ifmt_addi, { 0x66000000 }
  },
/* aaddl $rc5_0_a,$ra5_a,$rb5_a,$rc5_1_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RC5_0_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (RC5_1_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_aaddl, { 0x60800000 }
  },
/* asubl $rc5_0_a,$ra5_a,$rb5_a,$rc5_1_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RC5_0_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (RC5_1_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_aaddl, { 0x60800020 }
  },
/* ala $dh2_16_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DH2_16_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_ala, { 0x60200020 }
  },
/* alr $ra5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RA5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_alr, { 0x60000020 }
  },
/* alr2 $ra5_a,$rb5p_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RA5_A), ',', OP (RB5P_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_alr2, { 0x60000040 }
  },
/* asa $dh2_16_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DH2_16_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_ala, { 0x60300020 }
  },
/* asr $ra5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RA5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_alr, { 0x60100020 }
  },
/* aupi $im5_i_a,$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (IM5_I_A), ',', OP (IM5_M_A), 0 } },
    & ifmt_aupi, { 0x60400020 }
  },
/* amfar $rd5_a,$aridx5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD5_A), ',', OP (ARIDX5_A), 0 } },
    & ifmt_amfar, { 0x60300060 }
  },
/* amtar $ra5_a,$aridx5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RA5_A), ',', OP (ARIDX5_A), 0 } },
    & ifmt_amtar, { 0x60300040 }
  },
/* amtari $aridx4_a,$imm16_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (ARIDX4_A), ',', OP (IMM16_A), 0 } },
    & ifmt_amtari, { 0x60900000 }
  },
/* asats48 $d1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), 0 } },
    & ifmt_asats48, { 0x60200040 }
  },
/* awext $rd5_a,$d1_a,$lsbloc_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD5_A), ',', OP (D1_A), ',', OP (LSBLOC_A), 0 } },
    & ifmt_awext, { 0x60200060 }
  },
/* amadd $d1_a,$ra5_a,$rb5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), 0 } },
    & ifmt_amadd, { 0x60000000 }
  },
/* amaddl.s $d1_a,$ra5_a,$rb5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_s, { 0x60000080 }
  },
/* amaddl2.s $d1_a,$ra5_a,$rb5p_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_s, { 0x60000100 }
  },
/* amaddl.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x600000c0 }
  },
/* amaddl2.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60000140 }
  },
/* amaddsa $d1_a,$ra5_a,$rb5_a,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddsa, { 0x60000180 }
  },
/* amsub $d1_a,$ra5_a,$rb5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), 0 } },
    & ifmt_amadd, { 0x60100000 }
  },
/* amsubl.s $d1_a,$ra5_a,$rb5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_s, { 0x60100080 }
  },
/* amsubl2.s $d1_a,$ra5_a,$rb5p_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_s, { 0x60100100 }
  },
/* amsubl.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x601000c0 }
  },
/* amsubl2.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60100140 }
  },
/* amsubsa $d1_a,$ra5_a,$rb5_a,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddsa, { 0x60100180 }
  },
/* amadds $d1_a,$ra5_a,$rb5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), 0 } },
    & ifmt_amadd, { 0x60400000 }
  },
/* amaddsl.s $d1_a,$ra5_a,$rb5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_s, { 0x60400080 }
  },
/* amaddsl2.s $d1_a,$ra5_a,$rb5p_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_s, { 0x60400100 }
  },
/* amaddsl.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x604000c0 }
  },
/* amaddsl2.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60400140 }
  },
/* amaddssa $d1_a,$ra5_a,$rb5_a,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddsa, { 0x60400180 }
  },
/* amsubs $d1_a,$ra5_a,$rb5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), 0 } },
    & ifmt_amadd, { 0x60500000 }
  },
/* amsubsl.s $d1_a,$ra5_a,$rb5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_s, { 0x60500080 }
  },
/* amsubsl2.s $d1_a,$ra5_a,$rb5p_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_s, { 0x60500100 }
  },
/* amsubsl.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x605000c0 }
  },
/* amsubsl2.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60500140 }
  },
/* amsubssa $d1_a,$ra5_a,$rb5_a,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddsa, { 0x60500180 }
  },
/* amnegs $d1_a,$ra5_a,$rb5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), 0 } },
    & ifmt_amadd, { 0x60700000 }
  },
/* amnegsl.s $d1_a,$ra5_a,$rb5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_s, { 0x60700080 }
  },
/* amnegsl2.s $d1_a,$ra5_a,$rb5p_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_s, { 0x60700100 }
  },
/* amnegsl.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x607000c0 }
  },
/* amnegsl2.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60700140 }
  },
/* amnegssa $d1_a,$ra5_a,$rb5_a,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddsa, { 0x60700180 }
  },
/* amults $d1_a,$ra5_a,$rb5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), 0 } },
    & ifmt_amadd, { 0x60600000 }
  },
/* amultsl.s $d1_a,$ra5_a,$rb5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_s, { 0x60600080 }
  },
/* amultsl2.s $d1_a,$ra5_a,$rb5p_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_s, { 0x60600100 }
  },
/* amultsl.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x606000c0 }
  },
/* amultsl2.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60600140 }
  },
/* amultssa $d1_a,$ra5_a,$rb5_a,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddsa, { 0x60600180 }
  },
/* amult $d1_a,$ra5_a,$rb5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), 0 } },
    & ifmt_amadd, { 0x60200000 }
  },
/* amultl.s $d1_a,$ra5_a,$rb5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_s, { 0x60200080 }
  },
/* amultl2.s $d1_a,$ra5_a,$rb5p_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_s, { 0x60200100 }
  },
/* amultl.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x602000c0 }
  },
/* amultl2.l $d1_a,$r10a5_a,$r10b5_a,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60200140 }
  },
/* amultsa $d1_a,$ra5_a,$rb5_a,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddsa, { 0x60200180 }
  },
/* azol */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_azol, { 0x60200041 }
  },
/* amabbs $d1_a,$ra5_a_b,$rb5_a_b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_B), 0 } },
    & ifmt_amabbs, { 0x60000001 }
  },
/* amabts $d1_a,$ra5_a_b,$rb5_a_t */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_T), 0 } },
    & ifmt_amabts, { 0x60100001 }
  },
/* amatbs $d1_a,$ra5_a_t,$rb5_a_b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_B), 0 } },
    & ifmt_amatbs, { 0x60200001 }
  },
/* amatts $d1_a,$ra5_a_t,$rb5_a_t */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_T), 0 } },
    & ifmt_amatts, { 0x60300001 }
  },
/* ambbs $d1_a,$ra5_a_b,$rb5_a_b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_B), 0 } },
    & ifmt_amabbs, { 0x60400001 }
  },
/* ambts $d1_a,$ra5_a_b,$rb5_a_t */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_T), 0 } },
    & ifmt_amabts, { 0x60500001 }
  },
/* amtbs $d1_a,$ra5_a_t,$rb5_a_b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_B), 0 } },
    & ifmt_amatbs, { 0x60600001 }
  },
/* amtts $d1_a,$ra5_a_t,$rb5_a_t */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_T), 0 } },
    & ifmt_amatts, { 0x60700001 }
  },
/* amabbsl.s $d1_a,$ra5_a_b,$rb5_a_b,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_B), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amabbsl_s, { 0x61000080 }
  },
/* amabbsl.l $d1_a,$r10a5_a_b,$r10b5_a_b,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_B), ',', OP (R10B5_A_B), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x610000c0 }
  },
/* amabbsl2.s $d1_a,$ra5_a_b,$rb5p_a_b,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5P_A_B), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amabbsl2_s, { 0x61000100 }
  },
/* amabbsl2.l $d1_a,$r10a5_a_b,$r10b5_a_b,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_B), ',', OP (R10B5_A_B), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x61000140 }
  },
/* amabbssa $d1_a,$ra5_a_b,$rb5_a_b,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_B), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amabbssa, { 0x61000180 }
  },
/* amabtsl.s $d1_a,$ra5_a_b,$rb5_a_t,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_T), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amabtsl_s, { 0x61100080 }
  },
/* amabtsl.l $d1_a,$r10a5_a_b,$r10b5_a_t,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_B), ',', OP (R10B5_A_T), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x611000c0 }
  },
/* amabtsl2.s $d1_a,$ra5_a_b,$rb5p_a_t,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5P_A_T), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amabtsl2_s, { 0x61100100 }
  },
/* amabtsl2.l $d1_a,$r10a5_a_b,$r10b5_a_t,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_B), ',', OP (R10B5_A_T), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x61100140 }
  },
/* amabtssa $d1_a,$ra5_a_b,$rb5_a_t,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_T), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amabtssa, { 0x61100180 }
  },
/* amatbsl.s $d1_a,$ra5_a_t,$rb5_a_b,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_B), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amatbsl_s, { 0x61200080 }
  },
/* amatbsl.l $d1_a,$r10a5_a_t,$r10b5_a_b,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_T), ',', OP (R10B5_A_B), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x612000c0 }
  },
/* amatbsl2.s $d1_a,$ra5_a_t,$rb5p_a_b,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5P_A_B), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amatbsl2_s, { 0x61200100 }
  },
/* amatbsl2.l $d1_a,$r10a5_a_t,$r10b5_a_b,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_T), ',', OP (R10B5_A_B), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x61200140 }
  },
/* amatbssa $d1_a,$ra5_a_t,$rb5_a_b,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_B), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amatbssa, { 0x61200180 }
  },
/* amattsl.s $d1_a,$ra5_a_t,$rb5_a_t,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_T), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amattsl_s, { 0x61300080 }
  },
/* amattsl.l $d1_a,$r10a5_a_t,$r10b5_a_t,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_T), ',', OP (R10B5_A_T), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x613000c0 }
  },
/* amattsl2.s $d1_a,$ra5_a_t,$rb5p_a_t,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5P_A_T), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amattsl2_s, { 0x61300100 }
  },
/* amattsl2.l $d1_a,$r10a5_a_t,$r10b5_a_t,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_T), ',', OP (R10B5_A_T), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x61300140 }
  },
/* amattssa $d1_a,$ra5_a_t,$rb5_a_t,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_T), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amattssa, { 0x61300180 }
  },
/* ambbsl.s $d1_a,$ra5_a_b,$rb5_a_b,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_B), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amabbsl_s, { 0x61400080 }
  },
/* ambbsl.l $d1_a,$r10a5_a_b,$r10b5_a_b,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_B), ',', OP (R10B5_A_B), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x614000c0 }
  },
/* ambbsl2.s $d1_a,$ra5_a_b,$rb5p_a_b,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5P_A_B), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amabbsl2_s, { 0x61400100 }
  },
/* ambbsl2.l $d1_a,$r10a5_a_b,$r10b5_a_b,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_B), ',', OP (R10B5_A_B), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x61400140 }
  },
/* ambbssa $d1_a,$ra5_a_b,$rb5_a_b,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_B), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amabbssa, { 0x61400180 }
  },
/* ambtsl.s $d1_a,$ra5_a_b,$rb5_a_t,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_T), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amabtsl_s, { 0x61500080 }
  },
/* ambtsl.l $d1_a,$r10a5_a_b,$r10b5_a_t,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_B), ',', OP (R10B5_A_T), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x615000c0 }
  },
/* ambtsl2.s $d1_a,$ra5_a_b,$rb5p_a_t,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5P_A_T), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amabtsl2_s, { 0x61500100 }
  },
/* ambtsl2.l $d1_a,$r10a5_a_b,$r10b5_a_t,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_B), ',', OP (R10B5_A_T), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x61500140 }
  },
/* ambtssa $d1_a,$ra5_a_b,$rb5_a_t,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_B), ',', OP (RB5_A_T), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amabtssa, { 0x61500180 }
  },
/* amtbsl.s $d1_a,$ra5_a_t,$rb5_a_b,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_B), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amatbsl_s, { 0x61600080 }
  },
/* amtbsl.l $d1_a,$r10a5_a_t,$r10b5_a_b,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_T), ',', OP (R10B5_A_B), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x616000c0 }
  },
/* amtbsl2.s $d1_a,$ra5_a_t,$rb5p_a_b,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5P_A_B), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amatbsl2_s, { 0x61600100 }
  },
/* amtbsl2.l $d1_a,$r10a5_a_t,$r10b5_a_b,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_T), ',', OP (R10B5_A_B), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x61600140 }
  },
/* amtbssa $d1_a,$ra5_a_t,$rb5_a_b,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_B), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amatbssa, { 0x61600180 }
  },
/* amttsl.s $d1_a,$ra5_a_t,$rb5_a_t,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_T), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amattsl_s, { 0x61700080 }
  },
/* amttsl.l $d1_a,$r10a5_a_t,$r10b5_a_t,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_T), ',', OP (R10B5_A_T), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x617000c0 }
  },
/* amttsl2.s $d1_a,$ra5_a_t,$rb5p_a_t,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5P_A_T), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amattsl2_s, { 0x61700100 }
  },
/* amttsl2.l $d1_a,$r10a5_a_t,$r10b5_a_t,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A_T), ',', OP (R10B5_A_T), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x61700140 }
  },
/* amttssa $d1_a,$ra5_a_t,$rb5_a_t,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A_T), ',', OP (RB5_A_T), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amattssa, { 0x61700180 }
  },
/* amawbs $d1_a,$ra5_a,$rb5_a_b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_B), 0 } },
    & ifmt_amawbs, { 0x60400002 }
  },
/* amawts $d1_a,$ra5_a,$rb5_a_t */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_T), 0 } },
    & ifmt_amawts, { 0x60500002 }
  },
/* amwbs $d1_a,$ra5_a,$rb5_a_b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_B), 0 } },
    & ifmt_amawbs, { 0x60600002 }
  },
/* amwts $d1_a,$ra5_a,$rb5_a_t */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_T), 0 } },
    & ifmt_amawts, { 0x60700002 }
  },
/* amawbsl.s $d1_a,$ra5_a,$rb5_a_b,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_B), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amawbsl_s, { 0x60c00080 }
  },
/* amawbsl.l $d1_a,$r10a5_a,$r10b5_a_b,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A_B), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x60c000c0 }
  },
/* amawbsl2.s $d1_a,$ra5_a,$rb5p_a_b,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A_B), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amawbsl2_s, { 0x60c00100 }
  },
/* amawbsl2.l $d1_a,$r10a5_a,$r10b5_a_b,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A_B), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60c00140 }
  },
/* amawbssa $d1_a,$ra5_a,$rb5_a_b,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_B), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amawbssa, { 0x60c00180 }
  },
/* amawtsl.s $d1_a,$ra5_a,$rb5_a_t,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_T), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amawtsl_s, { 0x60d00080 }
  },
/* amawtsl.l $d1_a,$r10a5_a,$r10b5_a_t,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A_T), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x60d000c0 }
  },
/* amawtsl2.s $d1_a,$ra5_a,$rb5p_a_t,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A_T), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amawtsl2_s, { 0x60d00100 }
  },
/* amawtsl2.l $d1_a,$r10a5_a,$r10b5_a_t,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A_T), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60d00140 }
  },
/* amawtssa $d1_a,$ra5_a,$rb5_a_t,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_T), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amawtssa, { 0x60d00180 }
  },
/* amwbsl.s $d1_a,$ra5_a,$rb5_a_b,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_B), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amawbsl_s, { 0x60e00080 }
  },
/* amwbsl.l $d1_a,$r10a5_a,$r10b5_a_b,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A_B), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x60e000c0 }
  },
/* amwbsl2.s $d1_a,$ra5_a,$rb5p_a_b,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A_B), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amawbsl2_s, { 0x60e00100 }
  },
/* amwbsl2.l $d1_a,$r10a5_a,$r10b5_a_b,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A_B), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60e00140 }
  },
/* amwbssa $d1_a,$ra5_a,$rb5_a_b,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_B), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amawbssa, { 0x60e00180 }
  },
/* amwtsl.s $d1_a,$ra5_a,$rb5_a_t,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_T), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amawtsl_s, { 0x60f00080 }
  },
/* amwtsl.l $d1_a,$r10a5_a,$r10b5_a_t,$r10c5_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A_T), ',', OP (R10C5_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amaddl_l, { 0x60f000c0 }
  },
/* amwtsl2.s $d1_a,$ra5_a,$rb5p_a_t,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5P_A_T), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amawtsl2_s, { 0x60f00100 }
  },
/* amwtsl2.l $d1_a,$r10a5_a,$r10b5_a_t,$r10c5_0_a,$r10c5_1_a,[$im6_i_0_a],[$im6_i_1_a],$im6_m_0_a,$im6_m_1_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (R10A5_A), ',', OP (R10B5_A_T), ',', OP (R10C5_0_A), ',', OP (R10C5_1_A), ',', '[', OP (IM6_I_0_A), ']', ',', '[', OP (IM6_I_1_A), ']', ',', OP (IM6_M_0_A), ',', OP (IM6_M_1_A), 0 } },
    & ifmt_amaddl2_l, { 0x60f00140 }
  },
/* amwtssa $d1_a,$ra5_a,$rb5_a_t,$dh2_6_a,[$im5_i_a],$im5_m_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (D1_A), ',', OP (RA5_A), ',', OP (RB5_A_T), ',', OP (DH2_6_A), ',', '[', OP (IM5_I_A), ']', ',', OP (IM5_M_A), 0 } },
    & ifmt_amawtssa, { 0x60f00180 }
  },
/* amfar2 $rd5_a,$ar2idx5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD5_A), ',', OP (AR2IDX5_A), 0 } },
    & ifmt_amfar2, { 0x60300260 }
  },
/* amtar2 $rd5_a,$ar2idx5_a */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RD5_A), ',', OP (AR2IDX5_A), 0 } },
    & ifmt_amfar2, { 0x60300240 }
  },
/* fls $fsrt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_fls, { 0x6a000002 }
  },
/* fls.bi $fsrt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_fls, { 0x6a000082 }
  },
/* flsi $fsrt5,[$ra5+$slo12w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), '+', OP (SLO12W), ']', 0 } },
    & ifmt_flsi, { 0x30000000 }
  },
/* flsi.bi $fsrt5,[$ra5],$slo12w */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', ',', OP (SLO12W), 0 } },
    & ifmt_flsi, { 0x30001000 }
  },
/* fmfcfg $rt5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), 0 } },
    & ifmt_fmfcfg, { 0x6a000301 }
  },
/* fmfcsr $rt5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), 0 } },
    & ifmt_fmfcfg, { 0x6a000701 }
  },
/* fmtcsr $rt5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), 0 } },
    & ifmt_fmfcfg, { 0x6a000709 }
  },
/* fmfsr $rt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (FSRA5), 0 } },
    & ifmt_fmfsr, { 0x6a000001 }
  },
/* fmtsr $rt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (FSRA5), 0 } },
    & ifmt_fmfsr, { 0x6a000009 }
  },
/* fss $fsrt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_fls, { 0x6a00000a }
  },
/* fss.bi $fsrt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_fls, { 0x6a00008a }
  },
/* fssi $fsrt5,[$ra5+$slo12w] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), '+', OP (SLO12W), ']', 0 } },
    & ifmt_flsi, { 0x32000000 }
  },
/* fssi.bi $fsrt5,[$ra5],$slo12w */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', ',', OP (SLO12W), 0 } },
    & ifmt_flsi, { 0x32001000 }
  },
/* fs2d $fdrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fs2d, { 0x6a0003c0 }
  },
/* fabss $fsrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fabss, { 0x6a0017c0 }
  },
/* fadds $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000000 }
  },
/* fcmovns $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000180 }
  },
/* fcmovzs $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a0001c0 }
  },
/* fcmpeqs $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a000004 }
  },
/* fcmpeqs.e $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a000044 }
  },
/* fcmplts $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a000084 }
  },
/* fcmplts.e $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a0000c4 }
  },
/* fcmples $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a000104 }
  },
/* fcmples.e $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a000144 }
  },
/* fcmpuns $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a000184 }
  },
/* fcmpuns.e $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a0001c4 }
  },
/* fcpynss $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000080 }
  },
/* fcpyss $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a0000c0 }
  },
/* fdivs $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000340 }
  },
/* fmadds $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000100 }
  },
/* fmuls $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000300 }
  },
/* fmsubs $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000140 }
  },
/* fnmadds $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000200 }
  },
/* fnmsubs $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000240 }
  },
/* fs2si $fsrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fabss, { 0x6a0063c0 }
  },
/* fs2si.z $fsrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fabss, { 0x6a0073c0 }
  },
/* fs2ui $fsrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fabss, { 0x6a0043c0 }
  },
/* fs2ui.z $fsrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fabss, { 0x6a0053c0 }
  },
/* fsi2s $fsrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fabss, { 0x6a0033c0 }
  },
/* fsqrts $fsrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fabss, { 0x6a0007c0 }
  },
/* fsubs $fsrt5,$fsra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fadds, { 0x6a000040 }
  },
/* fui2s $fsrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fabss, { 0x6a0023c0 }
  },
/* fabsd $fdrt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), 0 } },
    & ifmt_fabsd, { 0x6a0017c8 }
  },
/* faddd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000008 }
  },
/* fcmovnd $fdrt5,$fdra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmovnd, { 0x6a000188 }
  },
/* fcmovzd $fdrt5,$fdra5,$fsrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FSRB5), 0 } },
    & ifmt_fcmovnd, { 0x6a0001c8 }
  },
/* fcmpeqd $fsrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a00000c }
  },
/* fcmpeqd.e $fsrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a00004c }
  },
/* fcmpltd $fsrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a00008c }
  },
/* fcmpltd.e $fsrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a0000cc }
  },
/* fcmpled $fsrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a00010c }
  },
/* fcmpled.e $fsrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a00014c }
  },
/* fcmpund $fsrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a00018c }
  },
/* fcmpund.e $fsrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_fcmpeqs, { 0x6a0001cc }
  },
/* fcpynsd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000088 }
  },
/* fcpysd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a0000c8 }
  },
/* fd2s $fsrt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), 0 } },
    & ifmt_fd2s, { 0x6a0003c8 }
  },
/* fd2si $fsrt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), 0 } },
    & ifmt_fd2s, { 0x6a0063c8 }
  },
/* fd2si.z $fsrt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), 0 } },
    & ifmt_fd2s, { 0x6a0073c8 }
  },
/* fd2ui $fsrt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), 0 } },
    & ifmt_fd2s, { 0x6a0043c8 }
  },
/* fd2ui.z $fsrt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', OP (FDRA5), 0 } },
    & ifmt_fd2s, { 0x6a0053c8 }
  },
/* fdivd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000348 }
  },
/* fld $fdrt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_fld, { 0x6a000003 }
  },
/* fld.bi $fdrt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_fld, { 0x6a000083 }
  },
/* fldi $fdrt5,[$ra5+$slo12d] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), '+', OP (SLO12D), ']', 0 } },
    & ifmt_fldi, { 0x34000000 }
  },
/* fldi.bi $fdrt5,[$ra5],$slo12d */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', ',', OP (SLO12D), 0 } },
    & ifmt_fldi, { 0x34001000 }
  },
/* fmaddd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000108 }
  },
/* fmfdr $rt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (FDRA5), 0 } },
    & ifmt_fmfdr, { 0x6a000041 }
  },
/* fmsubd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000148 }
  },
/* fmtdr $rt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (FDRA5), 0 } },
    & ifmt_fmfdr, { 0x6a000049 }
  },
/* fmuld $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000308 }
  },
/* fnmaddd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000208 }
  },
/* fnmsubd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000248 }
  },
/* fsd $fdrt5,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_fld, { 0x6a00000b }
  },
/* fsd.bi $fdrt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_fld, { 0x6a00008b }
  },
/* fsdi $fdrt5,[$ra5+$slo12d] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), '+', OP (SLO12D), ']', 0 } },
    & ifmt_fldi, { 0x36000000 }
  },
/* fsdi.bi $fdrt5,[$ra5],$slo12d */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', ',', OP (SLO12D), 0 } },
    & ifmt_fldi, { 0x36001000 }
  },
/* fsi2d $fdrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fs2d, { 0x6a0033c8 }
  },
/* fsqrtd $fdrt5,$fdra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), 0 } },
    & ifmt_fs2d, { 0x6a0007c8 }
  },
/* fsubd $fdrt5,$fdra5,$fdrb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FDRA5), ',', OP (FDRB5), 0 } },
    & ifmt_faddd, { 0x6a000048 }
  },
/* fui2d $fdrt5,$fsra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', OP (FSRA5), 0 } },
    & ifmt_fs2d, { 0x6a0023c8 }
  },
/* cpe1 cp1,$uimm19 */
  {
    { 0, 0, 0, 16 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000010 }
  },
/* cpe1 cp2,$uimm19 */
  {
    { 0, 0, 0, 16 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000020 }
  },
/* cpe1 cp3,$uimm19 */
  {
    { 0, 0, 0, 16 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000030 }
  },
/* cpe2 cp1,$uimm19 */
  {
    { 0, 0, 0, 17 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000014 }
  },
/* cpe2 cp2,$uimm19 */
  {
    { 0, 0, 0, 17 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000024 }
  },
/* cpe2 cp3,$uimm19 */
  {
    { 0, 0, 0, 17 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000034 }
  },
/* cpe3 cp1,$uimm19 */
  {
    { 0, 0, 0, 18 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000018 }
  },
/* cpe3 cp2,$uimm19 */
  {
    { 0, 0, 0, 18 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000028 }
  },
/* cpe3 cp3,$uimm19 */
  {
    { 0, 0, 0, 18 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a000038 }
  },
/* cpe4 cp1,$uimm19 */
  {
    { 0, 0, 0, 19 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a00001c }
  },
/* cpe4 cp2,$uimm19 */
  {
    { 0, 0, 0, 19 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a00002c }
  },
/* cpe4 cp3,$uimm19 */
  {
    { 0, 0, 0, 19 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (UIMM19), 0 } },
    & ifmt_cpe1_cp1, { 0x6a00003c }
  },
/* cpld cp1,$copdr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cpld_cp1, { 0x6a000013 }
  },
/* cpld.bi cp1,$copdr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cpld_cp1, { 0x6a000093 }
  },
/* cpldi cp1,$copdr,[$ra5+$slo12d] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (SLO12D), ']', 0 } },
    & ifmt_cpldi_cp1, { 0x34002000 }
  },
/* cpldi.bi cp1,$copdr,[$ra5],$slo12d */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (SLO12D), 0 } },
    & ifmt_cpldi_cp1, { 0x34003000 }
  },
/* cpld cp2,$copdr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cpld_cp1, { 0x6a000023 }
  },
/* cpld.bi cp2,$copdr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cpld_cp1, { 0x6a0000a3 }
  },
/* cpldi cp2,$copdr,[$ra5+$slo12d] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (SLO12D), ']', 0 } },
    & ifmt_cpldi_cp1, { 0x34004000 }
  },
/* cpldi.bi cp2,$copdr,[$ra5],$slo12d */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (SLO12D), 0 } },
    & ifmt_cpldi_cp1, { 0x34005000 }
  },
/* cpld cp3,$copdr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cpld_cp1, { 0x6a000033 }
  },
/* cpld.bi cp3,$copdr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cpld_cp1, { 0x6a0000b3 }
  },
/* cpldi cp3,$copdr,[$ra5+$slo12d] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (SLO12D), ']', 0 } },
    & ifmt_cpldi_cp1, { 0x34006000 }
  },
/* cpldi.bi cp3,$copdr,[$ra5],$slo12d */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (SLO12D), 0 } },
    & ifmt_cpldi_cp1, { 0x34007000 }
  },
/* cplw cp1,$copwr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cplw_cp1, { 0x6a000012 }
  },
/* cplw.bi cp1,$copwr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cplw_cp1, { 0x6a000092 }
  },
/* cplwi cp1,$copwr,[$ra5+$slo12w] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (SLO12W), ']', 0 } },
    & ifmt_cplwi_cp1, { 0x30002000 }
  },
/* cplwi.bi cp1,$copwr,[$ra5],$slo12w */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (SLO12W), 0 } },
    & ifmt_cplwi_cp1, { 0x30003000 }
  },
/* cplw cp2,$copwr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cplw_cp1, { 0x6a000022 }
  },
/* cplw.bi cp2,$copwr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cplw_cp1, { 0x6a0000a2 }
  },
/* cplwi cp2,$copwr,[$ra5+$slo12w] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (SLO12W), ']', 0 } },
    & ifmt_cplwi_cp1, { 0x30004000 }
  },
/* cplwi.bi cp2,$copwr,[$ra5],$slo12w */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (SLO12W), 0 } },
    & ifmt_cplwi_cp1, { 0x30005000 }
  },
/* cplw cp3,$copwr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cplw_cp1, { 0x6a000032 }
  },
/* cplw.bi cp3,$copwr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cplw_cp1, { 0x6a0000b2 }
  },
/* cplwi cp3,$copwr,[$ra5+$slo12w] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (SLO12W), ']', 0 } },
    & ifmt_cplwi_cp1, { 0x30006000 }
  },
/* cplwi.bi cp3,$copwr,[$ra5],$slo12w */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (SLO12W), 0 } },
    & ifmt_cplwi_cp1, { 0x30007000 }
  },
/* cpsd cp1,$copdr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cpld_cp1, { 0x6a00001b }
  },
/* cpsd.bi cp1,$copdr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cpld_cp1, { 0x6a00009b }
  },
/* cpsdi cp1,$copdr,[$ra5+$slo12d] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (SLO12D), ']', 0 } },
    & ifmt_cpldi_cp1, { 0x36002000 }
  },
/* cpsdi.bi cp1,$copdr,[$ra5],$slo12d */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (SLO12D), 0 } },
    & ifmt_cpldi_cp1, { 0x36003000 }
  },
/* cpsd cp2,$copdr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cpld_cp1, { 0x6a00002b }
  },
/* cpsd.bi cp2,$copdr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cpld_cp1, { 0x6a0000ab }
  },
/* cpsdi cp2,$copdr,[$ra5+$slo12d] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (SLO12D), ']', 0 } },
    & ifmt_cpldi_cp1, { 0x36004000 }
  },
/* cpsdi.bi cp2,$copdr,[$ra5],$slo12d */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (SLO12D), 0 } },
    & ifmt_cpldi_cp1, { 0x36005000 }
  },
/* cpsd cp3,$copdr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cpld_cp1, { 0x6a00003b }
  },
/* cpsd.bi cp3,$copdr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cpld_cp1, { 0x6a0000bb }
  },
/* cpsdi cp3,$copdr,[$ra5+$slo12d] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (SLO12D), ']', 0 } },
    & ifmt_cpldi_cp1, { 0x36006000 }
  },
/* cpsdi.bi cp3,$copdr,[$ra5],$slo12d */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (SLO12D), 0 } },
    & ifmt_cpldi_cp1, { 0x36007000 }
  },
/* cpsw cp1,$copwr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cplw_cp1, { 0x6a00001a }
  },
/* cpsw.bi cp1,$copwr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cplw_cp1, { 0x6a00009a }
  },
/* cpswi cp1,$copwr,[$ra5+$slo12w] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (SLO12W), ']', 0 } },
    & ifmt_cplwi_cp1, { 0x32002000 }
  },
/* cpswi.bi cp1,$copwr,[$ra5],$slo12w */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (SLO12W), 0 } },
    & ifmt_cplwi_cp1, { 0x32003000 }
  },
/* cpsw cp2,$copwr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cplw_cp1, { 0x6a00002a }
  },
/* cpsw.bi cp2,$copwr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cplw_cp1, { 0x6a0000aa }
  },
/* cpswi cp2,$copwr,[$ra5+$slo12w] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (SLO12W), ']', 0 } },
    & ifmt_cplwi_cp1, { 0x32004000 }
  },
/* cpswi.bi cp2,$copwr,[$ra5],$slo12w */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (SLO12W), 0 } },
    & ifmt_cplwi_cp1, { 0x32005000 }
  },
/* cpsw cp3,$copwr,[$ra5+$rb5<<$si] */
  {
    { 0, 0, 0, 20 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), '<', '<', OP (SI), ']', 0 } },
    & ifmt_cplw_cp1, { 0x6a00003a }
  },
/* cpsw.bi cp3,$copwr,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 21 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_cplw_cp1, { 0x6a0000ba }
  },
/* cpswi cp3,$copwr,[$ra5+$slo12w] */
  {
    { 0, 0, 0, 22 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (SLO12W), ']', 0 } },
    & ifmt_cplwi_cp1, { 0x32006000 }
  },
/* cpswi.bi cp3,$copwr,[$ra5],$slo12w */
  {
    { 0, 0, 0, 23 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (SLO12W), 0 } },
    & ifmt_cplwi_cp1, { 0x32007000 }
  },
/* mfcpd cp1,$rt5,$uimm12 */
  {
    { 0, 0, 0, 24 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000051 }
  },
/* mtcpd cp1,$rt5,$uimm12 */
  {
    { 0, 0, 0, 25 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000059 }
  },
/* mfcpd cp2,$rt5,$uimm12 */
  {
    { 0, 0, 0, 24 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000061 }
  },
/* mtcpd cp2,$rt5,$uimm12 */
  {
    { 0, 0, 0, 25 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000069 }
  },
/* mfcpd cp3,$rt5,$uimm12 */
  {
    { 0, 0, 0, 24 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000071 }
  },
/* mtcpd cp3,$rt5,$uimm12 */
  {
    { 0, 0, 0, 25 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000079 }
  },
/* mfcpw cp1,$rt5,$uimm12 */
  {
    { 0, 0, 0, 26 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000011 }
  },
/* mtcpw cp1,$rt5,$uimm12 */
  {
    { 0, 0, 0, 27 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000019 }
  },
/* mfcpw cp2,$rt5,$uimm12 */
  {
    { 0, 0, 0, 26 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000021 }
  },
/* mtcpw cp2,$rt5,$uimm12 */
  {
    { 0, 0, 0, 27 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000029 }
  },
/* mfcpw cp3,$rt5,$uimm12 */
  {
    { 0, 0, 0, 26 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000031 }
  },
/* mtcpw cp3,$rt5,$uimm12 */
  {
    { 0, 0, 0, 27 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a000039 }
  },
/* mfcppw cp1,$rt5,$uimm12 */
  {
    { 0, 0, 0, 28 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a0000d1 }
  },
/* mtcppw cp1,$rt5,$uimm12 */
  {
    { 0, 0, 0, 29 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a0000d9 }
  },
/* mfcppw cp2,$rt5,$uimm12 */
  {
    { 0, 0, 0, 28 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a0000e1 }
  },
/* mtcppw cp2,$rt5,$uimm12 */
  {
    { 0, 0, 0, 29 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a0000e9 }
  },
/* mfcppw cp3,$rt5,$uimm12 */
  {
    { 0, 0, 0, 28 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a0000f1 }
  },
/* mtcppw cp3,$rt5,$uimm12 */
  {
    { 0, 0, 0, 29 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (RT5), ',', OP (UIMM12), 0 } },
    & ifmt_mfcpd_cp1, { 0x6a0000f9 }
  },
/* ffb $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_ffb, { 0x4200000e }
  },
/* ffbi $rt5,$ra5,$uimm8_s */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (UIMM8_S), 0 } },
    & ifmt_ffbi, { 0x4200004e }
  },
/* ffmism $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_ffb, { 0x4200000f }
  },
/* flmism $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_ffb, { 0x4200004f }
  },
/* ffzmism $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_ffb, { 0x42000017 }
  },
/* kaddw $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000018 }
  },
/* ksubw $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000019 }
  },
/* kslraw $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x4200001a }
  },
/* kaddh $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000058 }
  },
/* ksubh $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000059 }
  },
/* kdmbb $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000014 }
  },
/* kdmbt $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000054 }
  },
/* kdmtb $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000094 }
  },
/* kdmtt $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x420000d4 }
  },
/* khmbb $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000114 }
  },
/* khmbt $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000154 }
  },
/* khmtb $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x42000194 }
  },
/* khmtt $rt5,$ra5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (RB5), 0 } },
    & ifmt_add, { 0x420001d4 }
  },
/* rdov $rt5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), 0 } },
    & ifmt_RDOV, { 0x420f0060 }
  },
/* clrov */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_RDOV, { 0x420f0061 }
  },
/* ifcall9 $disp9 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DISP9), 0 } },
    & ifmt_ifcall9, { 0xf800 }
  },
/* ifcall $disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DISP16), 0 } },
    & ifmt_ifcall, { 0x4e000000 }
  },
/* ifret */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_ifret, { 0x4a000060 }
  },
/* ex9.it $swid5 */
  {
    { 0, 0, 0, 30 },
    { { MNEM, ' ', OP (SWID5), 0 } },
    & ifmt_break16v3, { 0xdd40 }
  },
/* ex9.it $swid9 */
  {
    { 0, 0, 0, 30 },
    { { MNEM, ' ', OP (SWID9), 0 } },
    & ifmt_break16, { 0xea00 }
  },
};

#undef A
#undef OPERAND
#undef MNEM
#undef OP

/* Formats for ALIAS macro-insns.  */

#define F(f) & nds32_cgen_ifld_table[NDS32_##f]
static const CGEN_IFMT ifmt_neg ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_zeb ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_ULO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbi_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lb1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lb2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lb3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lb_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lb_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lb_p2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhi_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lh1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lh2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lh3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lh_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lh_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lh_p2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_lw1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lw2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lw3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_lw_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lw_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lw_p2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwup1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwup2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_swup1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_swup2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbsi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbsi_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbs1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbs2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbs3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbs_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbs_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbs_p2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhsi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhsi_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhs1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhs2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhs3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhs_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhs_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhs_p2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sbi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_sbi_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_sb1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sb2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sb3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15B) }, { 0 } }
};

static const CGEN_IFMT ifmt_sb_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sb_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sb_p2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_shi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_shi_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_sh1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sh2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sh3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15H) }, { 0 } }
};

static const CGEN_IFMT ifmt_sh_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sh_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sh_p2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_swi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_swi_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_sw1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sw2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sw3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_sw_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sw_p ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sw_p2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_bim2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_bd2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_bdm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_ai2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_aim2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_ad2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmw_adm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smw_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smw_bim2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smw_bd2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smw_bdm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smw_ai2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smw_aim2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smw_ad2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smw_adm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_llw1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_llw2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_scw1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_scw2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_ret2 ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32T3_RES10_7) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_jral2 ATTRIBUTE_UNUSED = {
  32, 32, 0xffff83ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_jral_iton2 ATTRIBUTE_UNUSED = {
  32, 32, 0xffff83ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_jral_ton2 ATTRIBUTE_UNUSED = {
  32, 32, 0xffff83ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_mfsr_alias ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_SR10) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_mtsr_alias ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_SR10) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_dprefi_d2 ATTRIBUTE_UNUSED = {
  32, 32, 0xff007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T2_ST4) }, { F (F_32_RA5) }, { F (F_32T2_SLO15D) }, { 0 } }
};

static const CGEN_IFMT ifmt_dprefi_w2 ATTRIBUTE_UNUSED = {
  32, 32, 0xff007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T2_ST4) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_dpref1 ATTRIBUTE_UNUSED = {
  32, 32, 0xff0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T2_ST4) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_dpref2 ATTRIBUTE_UNUSED = {
  32, 32, 0xff0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T2_ST4) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_dpref3 ATTRIBUTE_UNUSED = {
  32, 32, 0xff007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T2_ST4) }, { F (F_32_RA5) }, { F (F_32T2_SLO15W) }, { 0 } }
};

static const CGEN_IFMT ifmt_msync2 ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_RES12_12) }, { F (F_32T3_EXT3) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_trap2 ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_SWID15) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_teqz2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0fffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_SWID15) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_tnez2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0fffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_SWID15) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_break2 ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T3_SWID15) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_tlbop2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfff07c1f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_tlbop3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfffffc1f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_cctl1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007c1f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_4_17) }, { F (F_32TX_1_21) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_cctl2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfff07c1f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_4_17) }, { F (F_32TX_1_21) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_cctl3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfffffc1f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_4_17) }, { F (F_32TX_1_21) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_cctl4 ATTRIBUTE_UNUSED = {
  32, 32, 0xfff0781f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_4_17) }, { F (F_32TX_1_21) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_nop ATTRIBUTE_UNUSED = {
  32, 32, 0xffffffff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T3_UIMM5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi3332 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe07, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3W) }, { 0 } }
};

static const CGEN_IFMT ifmt_lhi3332 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe07, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3H) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbi3332 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe07, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3B) }, { 0 } }
};

static const CGEN_IFMT ifmt_swi3332 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe07, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3W) }, { 0 } }
};

static const CGEN_IFMT ifmt_shi3332 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe07, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3H) }, { 0 } }
};

static const CGEN_IFMT ifmt_sbi3332 ATTRIBUTE_UNUSED = {
  16, 16, 0xfe07, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT3_7) }, { F (F_16_RA3) }, { F (F_16_ULO3B) }, { 0 } }
};

static const CGEN_IFMT ifmt_lwi372 ATTRIBUTE_UNUSED = {
  16, 16, 0xf8ff, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_RT3) }, { F (F_16_OPC1431) }, { F (F_16_ULO7W) }, { 0 } }
};

static const CGEN_IFMT ifmt_swi372 ATTRIBUTE_UNUSED = {
  16, 16, 0xf8ff, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_RT3) }, { F (F_16_OPC1431) }, { F (F_16_ULO7W) }, { 0 } }
};

static const CGEN_IFMT ifmt_ret52 ATTRIBUTE_UNUSED = {
  16, 16, 0xffff, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_OPC1433) }, { F (F_16_RB5H) }, { 0 } }
};

static const CGEN_IFMT ifmt_nop16 ATTRIBUTE_UNUSED = {
  16, 16, 0xffff, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC142) }, { F (F_16_RT4) }, { F (F_16_UIMM5) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwa_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwa_bim2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwa_bd2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwa_bdm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwa_ai2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwa_aim2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwa_ad2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwa_adm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwa_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwa_bim2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwa_bd2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwa_bdm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwa_ai2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwa_aim2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwa_ad2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwa_adm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbup1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lbup2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sbup1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_sbup2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10DSI) }, { F (F_32T3_SUB10SI) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwzb_b2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwzb_bm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwzb_a2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_lmwzb_am2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwzb_b2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwzb_bm2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwzb_a2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_smwzb_am2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T5_MASK4) }, { F (F_32T5_SUB4) }, { F (F_32T5_RES2) }, { 0 } }
};

static const CGEN_IFMT ifmt_jralnez2 ATTRIBUTE_UNUSED = {
  32, 32, 0xffff83ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_cctl5 ATTRIBUTE_UNUSED = {
  32, 32, 0xfffff81f, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_4_17) }, { F (F_32TX_1_21) }, { F (F_32T4_EXT5) }, { F (F_32T4_SUB5) }, { 0 } }
};

static const CGEN_IFMT ifmt_beq_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe004000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SUB1) }, { F (F_32T2_DISP14) }, { 0 } }
};

static const CGEN_IFMT ifmt_bne_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe004000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32T2_SUB1) }, { F (F_32T2_DISP14) }, { 0 } }
};

static const CGEN_IFMT ifmt_beqz_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_bnez_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_bgez_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_bltz_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_bgtz_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_blez_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_beqs38_r ATTRIBUTE_UNUSED = {
  16, 16, 0xf800, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_RT3) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_bnes38_r ATTRIBUTE_UNUSED = {
  16, 16, 0xf800, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_RT3) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_beqz38_r ATTRIBUTE_UNUSED = {
  16, 16, 0xf800, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_RT3) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_bnez38_r ATTRIBUTE_UNUSED = {
  16, 16, 0xf800, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_RT3) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_beqzs8_r ATTRIBUTE_UNUSED = {
  16, 16, 0xff00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_bnezs8_r ATTRIBUTE_UNUSED = {
  16, 16, 0xff00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_bgezal_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_bltzal_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f0000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T1_SUB4) }, { F (F_32T1_DISP16) }, { 0 } }
};

static const CGEN_IFMT ifmt_j_r ATTRIBUTE_UNUSED = {
  32, 32, 0xff000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T0_DISP24) }, { 0 } }
};

static const CGEN_IFMT ifmt_j8_r ATTRIBUTE_UNUSED = {
  16, 16, 0xff00, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_HSDISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_jal_r ATTRIBUTE_UNUSED = {
  32, 32, 0xff000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T0_DISP24) }, { 0 } }
};

static const CGEN_IFMT ifmt_jral_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0f83ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10D) }, { F (F_32T3_SUB10G) }, { F (F_32T3_SUB10C) }, { 0 } }
};

static const CGEN_IFMT ifmt_jral5_r ATTRIBUTE_UNUSED = {
  16, 16, 0xffe0, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC143) }, { F (F_16_OPC1433) }, { F (F_16_RB5H) }, { 0 } }
};

static const CGEN_IFMT ifmt_beqc_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe080000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T21_SUB1) }, { F (F_32T2_SIMM11) }, { F (F_32T1_DISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_bnec_r ATTRIBUTE_UNUSED = {
  32, 32, 0xfe080000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32T21_SUB1) }, { F (F_32T2_SIMM11) }, { F (F_32T1_DISP8) }, { 0 } }
};

static const CGEN_IFMT ifmt_fls1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fls2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fls1_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fls2_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_flsi1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_flsi1_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_fss1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fss2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fss_bi1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fss_bi2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fld1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fld2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fld1_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fld2_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fldi1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_fldi1_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_fsd1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fsd2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fsd1_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_fsd2_bi ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp1_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp1_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp1_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp1_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpldi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpldi_bi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp2_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp2_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp2_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp2_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpldi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpldi_bi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp3_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_cp3_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp3_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpld_bi_cp3_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpldi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpldi_bi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp1_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp1_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp1_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp1_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplwi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplwi_bi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp2_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp2_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp2_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp2_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplwi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplwi_bi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp3_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_cp3_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp3_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplw_bi_cp3_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplwi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cplwi_bi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp1_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp1_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp1_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp1_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsdi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsdi_bi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp2_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp2_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp2_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp2_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsdi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsdi_bi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp3_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_cp3_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp3_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsd_bi_cp3_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsdi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsdi_bi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12D) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp1_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp1_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp1_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp1_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpswi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpswi_bi_cp1_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp2_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp2_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp2_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp2_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpswi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpswi_bi_cp2_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp3_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_cp3_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0000ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp3_2 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe0003ff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpsw_bi_cp3_3 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32_RB5) }, { F (F_32T3_SUB10SI) }, { F (F_32TX_1_24) }, { F (F_32TX_1_25) }, { F (F_32TX_2_26) }, { F (F_32TX_2_28) }, { F (F_32TX_2_30) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpswi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_cpswi_bi_cp3_1 ATTRIBUTE_UNUSED = {
  32, 32, 0xfe007fff, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_RT5) }, { F (F_32_RA5) }, { F (F_32TX_2_17) }, { F (F_32TX_1_19) }, { F (F_32TX_SLO12W) }, { 0 } }
};

static const CGEN_IFMT ifmt_ifret16 ATTRIBUTE_UNUSED = {
  16, 16, 0xffff, { { F (F_IFMT) }, { F (F_16_OPC14) }, { F (F_16_OPC141) }, { F (F_16_RT5H) }, { F (F_16_RA5H) }, { 0 } }
};

static const CGEN_IFMT ifmt_j_it ATTRIBUTE_UNUSED = {
  32, 32, 0xff000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T0_DISP24) }, { 0 } }
};

static const CGEN_IFMT ifmt_jal_it ATTRIBUTE_UNUSED = {
  32, 32, 0xff000000, { { F (F_IFMT) }, { F (F_32_OPC6G) }, { F (F_32_OPC6C) }, { F (F_32_SUB1) }, { F (F_32T0_DISP24) }, { 0 } }
};

#undef F

/* Each non-simple macro entry points to an array of expansion possibilities.  */

#define A(a) (1 << CGEN_INSN_##a)
#define OPERAND(op) NDS32_OPERAND_##op
#define MNEM CGEN_SYNTAX_MNEMONIC /* syntax value for mnemonic */
#define OP(field) CGEN_SYNTAX_MAKE_FIELD (OPERAND (field))

/* The macro instruction table.  */

static const CGEN_IBASE nds32_cgen_macro_insn_table[] =
{
/* neg $rt5,$ra5 */
  {
    -1, "neg", "neg", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* zeb $rt5,$ra5 */
  {
    -1, "zeb", "zeb", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* lbi $rt5,[$ra5] */
  {
    -1, "lbi2", "lbi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbi.p $rt5,[$ra5],$slo15b */
  {
    -1, "lbi.p", "lbi.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lb $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "lb1", "lb", 32,
    { 0|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lb $rt5,[$ra5+$rb5] */
  {
    -1, "lb2", "lb", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lb $rt5,[$ra5] */
  {
    -1, "lb3", "lb", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lb.bi $rt5,[$ra5],$rb5 */
  {
    -1, "lb.bi2", "lb.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lb.p $rt5,[$ra5],$rb5<<$si */
  {
    -1, "lb.p", "lb.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lb.p $rt5,[$ra5],$rb5 */
  {
    -1, "lb.p2", "lb.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhi $rt5,[$ra5] */
  {
    -1, "lhi2", "lhi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhi.p $rt5,[$ra5],$slo15h */
  {
    -1, "lhi.p", "lhi.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lh $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "lh1", "lh", 32,
    { 0|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lh $rt5,[$ra5+$rb5] */
  {
    -1, "lh2", "lh", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lh $rt5,[$ra5] */
  {
    -1, "lh3", "lh", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lh.bi $rt5,[$ra5],$rb5 */
  {
    -1, "lh.bi2", "lh.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lh.p $rt5,[$ra5],$rb5<<$si */
  {
    -1, "lh.p", "lh.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lh.p $rt5,[$ra5],$rb5 */
  {
    -1, "lh.p2", "lh.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lwi $rt5,[$ra5] */
  {
    -1, "lwi2", "lwi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lwi.p $rt5,[$ra5],$slo15w */
  {
    -1, "lwi.p", "lwi.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lw $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "lw1", "lw", 32,
    { 0|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lw $rt5,[$ra5+$rb5] */
  {
    -1, "lw2", "lw", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lw $rt5,[$ra5] */
  {
    -1, "lw3", "lw", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lw.bi $rt5,[$ra5],$rb5 */
  {
    -1, "lw.bi2", "lw.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lw.p $rt5,[$ra5],$rb5<<$si */
  {
    -1, "lw.p", "lw.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lw.p $rt5,[$ra5],$rb5 */
  {
    -1, "lw.p2", "lw.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lwup $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "lwup1", "lwup", 32,
    { 0|A(NOT_V3M)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lwup $rt5,[$ra5+$rb5] */
  {
    -1, "lwup2", "lwup", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* swup $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "swup1", "swup", 32,
    { 0|A(NOT_V3M)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* swup $rt5,[$ra5+$rb5] */
  {
    -1, "swup2", "swup", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbsi $rt5,[$ra5] */
  {
    -1, "lbsi2", "lbsi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbsi.p $rt5,[$ra5],$slo15b */
  {
    -1, "lbsi.p", "lbsi.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbs $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "lbs1", "lbs", 32,
    { 0|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbs $rt5,[$ra5+$rb5] */
  {
    -1, "lbs2", "lbs", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbs $rt5,[$ra5] */
  {
    -1, "lbs3", "lbs", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbs.bi $rt5,[$ra5],$rb5 */
  {
    -1, "lbs.bi2", "lbs.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbs.p $rt5,[$ra5],$rb5<<$si */
  {
    -1, "lbs.p", "lbs.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbs.p $rt5,[$ra5],$rb5 */
  {
    -1, "lbs.p2", "lbs.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhsi $rt5,[$ra5] */
  {
    -1, "lhsi2", "lhsi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhsi.p $rt5,[$ra5],$slo15h */
  {
    -1, "lhsi.p", "lhsi.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhs $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "lhs1", "lhs", 32,
    { 0|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhs $rt5,[$ra5+$rb5] */
  {
    -1, "lhs2", "lhs", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhs $rt5,[$ra5] */
  {
    -1, "lhs3", "lhs", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhs.bi $rt5,[$ra5],$rb5 */
  {
    -1, "lhs.bi2", "lhs.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhs.p $rt5,[$ra5],$rb5<<$si */
  {
    -1, "lhs.p", "lhs.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhs.p $rt5,[$ra5],$rb5 */
  {
    -1, "lhs.p2", "lhs.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sbi $rt5,[$ra5] */
  {
    -1, "sbi2", "sbi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sbi.p $rt5,[$ra5],$slo15b */
  {
    -1, "sbi.p", "sbi.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sb $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "sb1", "sb", 32,
    { 0|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sb $rt5,[$ra5+$rb5] */
  {
    -1, "sb2", "sb", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sb $rt5,[$ra5] */
  {
    -1, "sb3", "sb", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sb.bi $rt5,[$ra5],$rb5 */
  {
    -1, "sb.bi2", "sb.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sb.p $rt5,[$ra5],$rb5<<$si */
  {
    -1, "sb.p", "sb.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sb.p $rt5,[$ra5],$rb5 */
  {
    -1, "sb.p2", "sb.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* shi $rt5,[$ra5] */
  {
    -1, "shi2", "shi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* shi.p $rt5,[$ra5],$slo15h */
  {
    -1, "shi.p", "shi.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sh $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "sh1", "sh", 32,
    { 0|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sh $rt5,[$ra5+$rb5] */
  {
    -1, "sh2", "sh", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sh $rt5,[$ra5] */
  {
    -1, "sh3", "sh", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sh.bi $rt5,[$ra5],$rb5 */
  {
    -1, "sh.bi2", "sh.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sh.p $rt5,[$ra5],$rb5<<$si */
  {
    -1, "sh.p", "sh.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sh.p $rt5,[$ra5],$rb5 */
  {
    -1, "sh.p2", "sh.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* swi $rt5,[$ra5] */
  {
    -1, "swi2", "swi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* swi.p $rt5,[$ra5],$slo15w */
  {
    -1, "swi.p", "swi.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sw $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "sw1", "sw", 32,
    { 0|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sw $rt5,[$ra5+$rb5] */
  {
    -1, "sw2", "sw", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sw $rt5,[$ra5] */
  {
    -1, "sw3", "sw", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sw.bi $rt5,[$ra5],$rb5 */
  {
    -1, "sw.bi2", "sw.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sw.p $rt5,[$ra5],$rb5<<$si */
  {
    -1, "sw.p", "sw.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sw.p $rt5,[$ra5],$rb5 */
  {
    -1, "sw.p2", "sw.p", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmw.bi $rt5,[$ra5],$rb5 */
  {
    -1, "lmw.bi2", "lmw.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmw.bim $rt5,[$ra5],$rb5 */
  {
    -1, "lmw.bim2", "lmw.bim", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmw.bd $rt5,[$ra5],$rb5 */
  {
    -1, "lmw.bd2", "lmw.bd", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmw.bdm $rt5,[$ra5],$rb5 */
  {
    -1, "lmw.bdm2", "lmw.bdm", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmw.ai $rt5,[$ra5],$rb5 */
  {
    -1, "lmw.ai2", "lmw.ai", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmw.aim $rt5,[$ra5],$rb5 */
  {
    -1, "lmw.aim2", "lmw.aim", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmw.ad $rt5,[$ra5],$rb5 */
  {
    -1, "lmw.ad2", "lmw.ad", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmw.adm $rt5,[$ra5],$rb5 */
  {
    -1, "lmw.adm2", "lmw.adm", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smw.bi $rt5,[$ra5],$rb5 */
  {
    -1, "smw.bi2", "smw.bi", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smw.bim $rt5,[$ra5],$rb5 */
  {
    -1, "smw.bim2", "smw.bim", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smw.bd $rt5,[$ra5],$rb5 */
  {
    -1, "smw.bd2", "smw.bd", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smw.bdm $rt5,[$ra5],$rb5 */
  {
    -1, "smw.bdm2", "smw.bdm", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smw.ai $rt5,[$ra5],$rb5 */
  {
    -1, "smw.ai2", "smw.ai", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smw.aim $rt5,[$ra5],$rb5 */
  {
    -1, "smw.aim2", "smw.aim", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smw.ad $rt5,[$ra5],$rb5 */
  {
    -1, "smw.ad2", "smw.ad", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smw.adm $rt5,[$ra5],$rb5 */
  {
    -1, "smw.adm2", "smw.adm", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* llw $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "llw1", "llw", 32,
    { 0|A(NOT_V3M)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* llw $rt5,[$ra5+$rb5] */
  {
    -1, "llw2", "llw", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* scw $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "scw1", "scw", 32,
    { 0|A(NOT_V3M)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* scw $rt5,[$ra5+$rb5] */
  {
    -1, "scw2", "scw", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* ret */
  {
    -1, "ret2", "ret", 32,
    { 0|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* jral $rb5 */
  {
    -1, "jral2", "jral", 32,
    { 0|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* jral.iton $rb5 */
  {
    -1, "jral.iton2", "jral.iton", 32,
    { 0|A(NOT_V3M)|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* jral.ton $rb5 */
  {
    -1, "jral.ton2", "jral.ton", 32,
    { 0|A(NOT_V3M)|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* mfsr $rt5,$uimm_sr10 */
  {
    -1, "mfsr_alias", "mfsr", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* mtsr $rt5,$uimm_sr10 */
  {
    -1, "mtsr_alias", "mtsr", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* dprefi.d $dprefst,[$ra5] */
  {
    -1, "dprefi.d2", "dprefi.d", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* dprefi.w $dprefst,[$ra5] */
  {
    -1, "dprefi.w2", "dprefi.w", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* dpref $dprefst,[$ra5+($rb5<<$si)] */
  {
    -1, "dpref1", "dpref", 32,
    { 0|A(NOT_V3M)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* dpref $dprefst,[$ra5+$rb5] */
  {
    -1, "dpref2", "dpref", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* dpref $dprefst,[$ra5] */
  {
    -1, "dpref3", "dpref", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* msync */
  {
    -1, "msync2", "msync", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* trap */
  {
    -1, "trap2", "trap", 32,
    { 0|A(NOT_V3M)|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* teqz $rt5 */
  {
    -1, "teqz2", "teqz", 32,
    { 0|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* tnez $rt5 */
  {
    -1, "tnez2", "tnez", 32,
    { 0|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* break */
  {
    -1, "break2", "break", 32,
    { 0|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* tlbop $ra5,$tlbopst */
  {
    -1, "tlbop2", "tlbop", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* tlbop $tlbopst */
  {
    -1, "tlbop3", "tlbop", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* cctl $rt5,$ra5,$cctlst */
  {
    -1, "cctl1", "cctl", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* cctl $ra5,$cctlst */
  {
    -1, "cctl2", "cctl", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* cctl $cctlst */
  {
    -1, "cctl3", "cctl", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* cctl $ra5,$cctlst,$cctllvl */
  {
    -1, "cctl4", "cctl", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* nop */
  {
    -1, "nop", "nop", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* lwi333 $rt3_7,[$ra3] */
  {
    -1, "lwi3332", "lwi333", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lhi333 $rt3_7,[$ra3] */
  {
    -1, "lhi3332", "lhi333", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lbi333 $rt3_7,[$ra3] */
  {
    -1, "lbi3332", "lbi333", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* swi333 $rt3_7,[$ra3] */
  {
    -1, "swi3332", "swi333", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* shi333 $rt3_7,[$ra3] */
  {
    -1, "shi3332", "shi333", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* sbi333 $rt3_7,[$ra3] */
  {
    -1, "sbi3332", "sbi333", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lwi37 $rt3,[\$fp] */
  {
    -1, "lwi372", "lwi37", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* swi37 $rt3,[\$fp] */
  {
    -1, "swi372", "swi37", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* ret5 */
  {
    -1, "ret52", "ret5", 16,
    { 0|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* nop16 */
  {
    -1, "nop16", "nop16", 16,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* lmwa.bi $rt5,[$ra5],$rb5 */
  {
    -1, "lmwa.bi2", "lmwa.bi", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lmwa.bim $rt5,[$ra5],$rb5 */
  {
    -1, "lmwa.bim2", "lmwa.bim", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lmwa.bd $rt5,[$ra5],$rb5 */
  {
    -1, "lmwa.bd2", "lmwa.bd", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lmwa.bdm $rt5,[$ra5],$rb5 */
  {
    -1, "lmwa.bdm2", "lmwa.bdm", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lmwa.ai $rt5,[$ra5],$rb5 */
  {
    -1, "lmwa.ai2", "lmwa.ai", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lmwa.aim $rt5,[$ra5],$rb5 */
  {
    -1, "lmwa.aim2", "lmwa.aim", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lmwa.ad $rt5,[$ra5],$rb5 */
  {
    -1, "lmwa.ad2", "lmwa.ad", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lmwa.adm $rt5,[$ra5],$rb5 */
  {
    -1, "lmwa.adm2", "lmwa.adm", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* smwa.bi $rt5,[$ra5],$rb5 */
  {
    -1, "smwa.bi2", "smwa.bi", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* smwa.bim $rt5,[$ra5],$rb5 */
  {
    -1, "smwa.bim2", "smwa.bim", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* smwa.bd $rt5,[$ra5],$rb5 */
  {
    -1, "smwa.bd2", "smwa.bd", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* smwa.bdm $rt5,[$ra5],$rb5 */
  {
    -1, "smwa.bdm2", "smwa.bdm", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* smwa.ai $rt5,[$ra5],$rb5 */
  {
    -1, "smwa.ai2", "smwa.ai", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* smwa.aim $rt5,[$ra5],$rb5 */
  {
    -1, "smwa.aim2", "smwa.aim", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* smwa.ad $rt5,[$ra5],$rb5 */
  {
    -1, "smwa.ad2", "smwa.ad", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* smwa.adm $rt5,[$ra5],$rb5 */
  {
    -1, "smwa.adm2", "smwa.adm", 32,
    { 0|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lbup $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "lbup1", "lbup", 32,
    { 0|A(NOT_V3M)|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lbup $rt5,[$ra5+$rb5] */
  {
    -1, "lbup2", "lbup", 32,
    { 0|A(NOT_V3M)|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* sbup $rt5,[$ra5+($rb5<<$si)] */
  {
    -1, "sbup1", "sbup", 32,
    { 0|A(NOT_V3M)|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* sbup $rt5,[$ra5+$rb5] */
  {
    -1, "sbup2", "sbup", 32,
    { 0|A(NOT_V3M)|A(A32V2)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* lmwzb.b $rt5,[$ra5],$rb5 */
  {
    -1, "lmwzb.b2", "lmwzb.b", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmwzb.bm $rt5,[$ra5],$rb5 */
  {
    -1, "lmwzb.bm2", "lmwzb.bm", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmwzb.a $rt5,[$ra5],$rb5 */
  {
    -1, "lmwzb.a2", "lmwzb.a", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* lmwzb.am $rt5,[$ra5],$rb5 */
  {
    -1, "lmwzb.am2", "lmwzb.am", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smwzb.b $rt5,[$ra5],$rb5 */
  {
    -1, "smwzb.b2", "smwzb.b", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smwzb.bm $rt5,[$ra5],$rb5 */
  {
    -1, "smwzb.bm2", "smwzb.bm", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smwzb.a $rt5,[$ra5],$rb5 */
  {
    -1, "smwzb.a2", "smwzb.a", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* smwzb.am $rt5,[$ra5],$rb5 */
  {
    -1, "smwzb.am2", "smwzb.am", 32,
    { 0|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_O, 0 } } } }
  },
/* jralnez $rb5 */
  {
    -1, "jralnez2", "jralnez", 32,
    { 0|A(NOT_V3M)|A(V3)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cctl $cctlst,$cctllvl */
  {
    -1, "cctl5", "cctl", 32,
    { 0|A(NOT_V3M)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* beq_r $rt5,$ra5,$disp14 */
  {
    -1, "beq_r", "beq_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bne_r $rt5,$ra5,$disp14 */
  {
    -1, "bne_r", "bne_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* beqz_r $rt5,$disp16 */
  {
    -1, "beqz_r", "beqz_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bnez_r $rt5,$disp16 */
  {
    -1, "bnez_r", "bnez_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bgez_r $rt5,$disp16 */
  {
    -1, "bgez_r", "bgez_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bltz_r $rt5,$disp16 */
  {
    -1, "bltz_r", "bltz_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bgtz_r $rt5,$disp16 */
  {
    -1, "bgtz_r", "bgtz_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* blez_r $rt5,$disp16 */
  {
    -1, "blez_r", "blez_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* beqs38_r $rt3,$hsdisp8 */
  {
    -1, "beqs38_r", "beqs38_r", 16,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bnes38_r $rt3,$hsdisp8 */
  {
    -1, "bnes38_r", "bnes38_r", 16,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* beqz38_r $rt3,$hsdisp8 */
  {
    -1, "beqz38_r", "beqz38_r", 16,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bnez38_r $rt3,$hsdisp8 */
  {
    -1, "bnez38_r", "bnez38_r", 16,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* beqzs8_r $hsdisp8 */
  {
    -1, "beqzs8_r", "beqzs8_r", 16,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bnezs8_r $hsdisp8 */
  {
    -1, "bnezs8_r", "bnezs8_r", 16,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bgezal_r $rt5,$disp16 */
  {
    -1, "bgezal_r", "bgezal_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bltzal_r $rt5,$disp16 */
  {
    -1, "bltzal_r", "bltzal_r", 32,
    { 0|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* j_r $disp24 */
  {
    -1, "j_r", "j_r", 32,
    { 0|A(RELAXABLE)|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* j8_r $hsdisp8 */
  {
    -1, "j8_r", "j8_r", 16,
    { 0|A(RELAXABLE)|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* jal_r $disp24 */
  {
    -1, "jal_r", "jal_r", 32,
    { 0|A(RELAXABLE)|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* jral_r $rt5,$rb5 */
  {
    -1, "jral_r", "jral_r", 32,
    { 0|A(RELAXABLE)|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* jral5_r $rb5h */
  {
    -1, "jral5_r", "jral5_r", 16,
    { 0|A(RELAXABLE)|A(UNCOND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* beqc_r $rt5,$simm11,$disp8 */
  {
    -1, "beqc_r", "beqc_r", 32,
    { 0|A(V3)|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* bnec_r $rt5,$simm11,$disp8 */
  {
    -1, "bnec_r", "bnec_r", 32,
    { 0|A(V3)|A(RELAXABLE)|A(COND_CTI)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fls $fsrt5,[$ra5+($rb5<<$si)] */
  {
    -1, "fls1", "fls", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fls $fsrt5,[$ra5+$rb5] */
  {
    -1, "fls2", "fls", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fls.bi $fsrt5,[$ra5],($rb5<<$si) */
  {
    -1, "fls1.bi", "fls.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fls.bi $fsrt5,[$ra5],$rb5 */
  {
    -1, "fls2.bi", "fls.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* flsi $fsrt5,[$ra5] */
  {
    -1, "flsi1", "flsi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* flsi1.bi $fsrt5,[$ra5] */
  {
    -1, "flsi1.bi", "flsi1.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fss $fsrt5,[$ra5+($rb5<<$si)] */
  {
    -1, "fss1", "fss", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fss $fsrt5,[$ra5+$rb5] */
  {
    -1, "fss2", "fss", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fss.bi $fsrt5,[$ra5],($rb5<<$si) */
  {
    -1, "fss.bi1", "fss.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fss.bi $fsrt5,[$ra5],$rb5 */
  {
    -1, "fss.bi2", "fss.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fld $fdrt5,[$ra5+($rb5<<$si)] */
  {
    -1, "fld1", "fld", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fld $fdrt5,[$ra5+$rb5] */
  {
    -1, "fld2", "fld", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fld.bi $fdrt5,[$ra5],($rb5<<$si) */
  {
    -1, "fld1.bi", "fld.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fld.bi $fdrt5,[$ra5],$rb5 */
  {
    -1, "fld2.bi", "fld.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fldi $fdrt5,[$ra5] */
  {
    -1, "fldi1", "fldi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fldi.bi $fdrt5,[$ra5] */
  {
    -1, "fldi1.bi", "fldi.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fsd $fdrt5,[$ra5+($rb5<<$si)] */
  {
    -1, "fsd1", "fsd", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fsd $fdrt5,[$ra5+$rb5] */
  {
    -1, "fsd2", "fsd", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fsd.bi $fdrt5,[$ra5],($rb5<<$si) */
  {
    -1, "fsd1.bi", "fsd.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* fsd.bi $fdrt5,[$ra5],$rb5 */
  {
    -1, "fsd2.bi", "fsd.bi", 32,
    { 0|A(FPU_COM)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp1,$copdr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpld_cp1_1", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp1,$copdr,[$ra5+$rb5] */
  {
    -1, "cpld_cp1_2", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp1,$copdr,[$ra5] */
  {
    -1, "cpld_cp1_3", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp1,$copdr,[$ra5],($rb5<<$si) */
  {
    -1, "cpld.bi_cp1_1", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp1,$copdr,[$ra5],$rb5 */
  {
    -1, "cpld.bi_cp1_2", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp1,$copdr,[$ra5] */
  {
    -1, "cpld.bi_cp1_3", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpldi cp1,$copdr,[$ra5] */
  {
    -1, "cpldi_cp1_1", "cpldi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpldi.bi cp1,$copdr,[$ra5] */
  {
    -1, "cpldi.bi_cp1_1", "cpldi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp2,$copdr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpld_cp2_1", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp2,$copdr,[$ra5+$rb5] */
  {
    -1, "cpld_cp2_2", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp2,$copdr,[$ra5] */
  {
    -1, "cpld_cp2_3", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp2,$copdr,[$ra5],($rb5<<$si) */
  {
    -1, "cpld.bi_cp2_1", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp2,$copdr,[$ra5],$rb5 */
  {
    -1, "cpld.bi_cp2_2", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp2,$copdr,[$ra5] */
  {
    -1, "cpld.bi_cp2_3", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpldi cp2,$copdr,[$ra5] */
  {
    -1, "cpldi_cp2_1", "cpldi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpldi.bi cp2,$copdr,[$ra5] */
  {
    -1, "cpldi.bi_cp2_1", "cpldi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp3,$copdr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpld_cp3_1", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp3,$copdr,[$ra5+$rb5] */
  {
    -1, "cpld_cp3_2", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld cp3,$copdr,[$ra5] */
  {
    -1, "cpld_cp3_3", "cpld", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp3,$copdr,[$ra5],($rb5<<$si) */
  {
    -1, "cpld.bi_cp3_1", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp3,$copdr,[$ra5],$rb5 */
  {
    -1, "cpld.bi_cp3_2", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpld.bi cp3,$copdr,[$ra5] */
  {
    -1, "cpld.bi_cp3_3", "cpld.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpldi cp3,$copdr,[$ra5] */
  {
    -1, "cpldi_cp3_1", "cpldi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpldi.bi cp3,$copdr,[$ra5] */
  {
    -1, "cpldi.bi_cp3_1", "cpldi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp1,$copwr,[$ra5+($rb5<<$si)] */
  {
    -1, "cplw_cp1_1", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp1,$copwr,[$ra5+$rb5] */
  {
    -1, "cplw_cp1_2", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp1,$copwr,[$ra5] */
  {
    -1, "cplw_cp1_3", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp1,$copwr,[$ra5],($rb5<<$si) */
  {
    -1, "cplw.bi_cp1_1", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp1,$copwr,[$ra5],$rb5 */
  {
    -1, "cplw.bi_cp1_2", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp1,$copwr,[$ra5] */
  {
    -1, "cplw.bi_cp1_3", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplwi cp1,$copwr,[$ra5] */
  {
    -1, "cplwi_cp1_1", "cplwi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplwi.bi cp1,$copwr,[$ra5] */
  {
    -1, "cplwi.bi_cp1_1", "cplwi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp2,$copwr,[$ra5+($rb5<<$si)] */
  {
    -1, "cplw_cp2_1", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp2,$copwr,[$ra5+$rb5] */
  {
    -1, "cplw_cp2_2", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp2,$copwr,[$ra5] */
  {
    -1, "cplw_cp2_3", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp2,$copwr,[$ra5],($rb5<<$si) */
  {
    -1, "cplw.bi_cp2_1", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp2,$copwr,[$ra5],$rb5 */
  {
    -1, "cplw.bi_cp2_2", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp2,$copwr,[$ra5] */
  {
    -1, "cplw.bi_cp2_3", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplwi cp2,$copwr,[$ra5] */
  {
    -1, "cplwi_cp2_1", "cplwi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplwi.bi cp2,$copwr,[$ra5] */
  {
    -1, "cplwi.bi_cp2_1", "cplwi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp3,$copwr,[$ra5+($rb5<<$si)] */
  {
    -1, "cplw_cp3_1", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp3,$copwr,[$ra5+$rb5] */
  {
    -1, "cplw_cp3_2", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw cp3,$copwr,[$ra5] */
  {
    -1, "cplw_cp3_3", "cplw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp3,$copwr,[$ra5],($rb5<<$si) */
  {
    -1, "cplw.bi_cp3_1", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp3,$copwr,[$ra5],$rb5 */
  {
    -1, "cplw.bi_cp3_2", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplw.bi cp3,$copwr,[$ra5] */
  {
    -1, "cplw.bi_cp3_3", "cplw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplwi cp3,$copwr,[$ra5] */
  {
    -1, "cplwi_cp3_1", "cplwi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cplwi.bi cp3,$copwr,[$ra5] */
  {
    -1, "cplwi.bi_cp3_1", "cplwi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp1,$copdr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpsd_cp1_1", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp1,$copdr,[$ra5+$rb5] */
  {
    -1, "cpsd_cp1_2", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp1,$copdr,[$ra5] */
  {
    -1, "cpsd_cp1_3", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp1,$copdr,[$ra5],($rb5<<$si) */
  {
    -1, "cpsd.bi_cp1_1", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp1,$copdr,[$ra5],$rb5 */
  {
    -1, "cpsd.bi_cp1_2", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp1,$copdr,[$ra5] */
  {
    -1, "cpsd.bi_cp1_3", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsdi cp1,$copdr,[$ra5] */
  {
    -1, "cpsdi_cp1_1", "cpsdi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsdi.bi cp1,$copdr,[$ra5] */
  {
    -1, "cpsdi.bi_cp1_1", "cpsdi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp2,$copdr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpsd_cp2_1", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp2,$copdr,[$ra5+$rb5] */
  {
    -1, "cpsd_cp2_2", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp2,$copdr,[$ra5] */
  {
    -1, "cpsd_cp2_3", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp2,$copdr,[$ra5],($rb5<<$si) */
  {
    -1, "cpsd.bi_cp2_1", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp2,$copdr,[$ra5],$rb5 */
  {
    -1, "cpsd.bi_cp2_2", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp2,$copdr,[$ra5] */
  {
    -1, "cpsd.bi_cp2_3", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsdi cp2,$copdr,[$ra5] */
  {
    -1, "cpsdi_cp2_1", "cpsdi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsdi.bi cp2,$copdr,[$ra5] */
  {
    -1, "cpsdi.bi_cp2_1", "cpsdi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp3,$copdr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpsd_cp3_1", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp3,$copdr,[$ra5+$rb5] */
  {
    -1, "cpsd_cp3_2", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd cp3,$copdr,[$ra5] */
  {
    -1, "cpsd_cp3_3", "cpsd", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp3,$copdr,[$ra5],($rb5<<$si) */
  {
    -1, "cpsd.bi_cp3_1", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp3,$copdr,[$ra5],$rb5 */
  {
    -1, "cpsd.bi_cp3_2", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsd.bi cp3,$copdr,[$ra5] */
  {
    -1, "cpsd.bi_cp3_3", "cpsd.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsdi cp3,$copdr,[$ra5] */
  {
    -1, "cpsdi_cp3_1", "cpsdi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsdi.bi cp3,$copdr,[$ra5] */
  {
    -1, "cpsdi.bi_cp3_1", "cpsdi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp1,$copwr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpsw_cp1_1", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp1,$copwr,[$ra5+$rb5] */
  {
    -1, "cpsw_cp1_2", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp1,$copwr,[$ra5] */
  {
    -1, "cpsw_cp1_3", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp1,$copwr,[$ra5],($rb5<<$si) */
  {
    -1, "cpsw.bi_cp1_1", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp1,$copwr,[$ra5],$rb5 */
  {
    -1, "cpsw.bi_cp1_2", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp1,$copwr,[$ra5] */
  {
    -1, "cpsw.bi_cp1_3", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpswi cp1,$copwr,[$ra5] */
  {
    -1, "cpswi_cp1_1", "cpswi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpswi.bi cp1,$copwr,[$ra5] */
  {
    -1, "cpswi.bi_cp1_1", "cpswi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp2,$copwr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpsw_cp2_1", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp2,$copwr,[$ra5+$rb5] */
  {
    -1, "cpsw_cp2_2", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp2,$copwr,[$ra5] */
  {
    -1, "cpsw_cp2_3", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp2,$copwr,[$ra5],($rb5<<$si) */
  {
    -1, "cpsw.bi_cp2_1", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp2,$copwr,[$ra5],$rb5 */
  {
    -1, "cpsw.bi_cp2_2", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp2,$copwr,[$ra5] */
  {
    -1, "cpsw.bi_cp2_3", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpswi cp2,$copwr,[$ra5] */
  {
    -1, "cpswi_cp2_1", "cpswi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpswi.bi cp2,$copwr,[$ra5] */
  {
    -1, "cpswi.bi_cp2_1", "cpswi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp3,$copwr,[$ra5+($rb5<<$si)] */
  {
    -1, "cpsw_cp3_1", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp3,$copwr,[$ra5+$rb5] */
  {
    -1, "cpsw_cp3_2", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw cp3,$copwr,[$ra5] */
  {
    -1, "cpsw_cp3_3", "cpsw", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp3,$copwr,[$ra5],($rb5<<$si) */
  {
    -1, "cpsw.bi_cp3_1", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp3,$copwr,[$ra5],$rb5 */
  {
    -1, "cpsw.bi_cp3_2", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpsw.bi cp3,$copwr,[$ra5] */
  {
    -1, "cpsw.bi_cp3_3", "cpsw.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpswi cp3,$copwr,[$ra5] */
  {
    -1, "cpswi_cp3_1", "cpswi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* cpswi.bi cp3,$copwr,[$ra5] */
  {
    -1, "cpswi.bi_cp3_1", "cpswi.bi", 32,
    { 0|A(NO_DIS)|A(COP)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* ifret16 */
  {
    -1, "ifret16", "ifret16", 16,
    { 0|A(V3)|A(IFCEXT)|A(ALIAS), { { { (1<<MACH_N1H_V3), 0 } }, { { PIPE_NONE, 0 } } } }
  },
/* j.it $concat24 */
  {
    -1, "j.it", "j.it", 32,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
/* jal.it $concat24 */
  {
    -1, "jal.it", "jal.it", 32,
    { 0|A(A16)|A(NO_DIS)|A(ALIAS), { { { (1<<MACH_BASE), 0 } }, { { PIPE_OS, 0 } } } }
  },
};

/* The macro instruction opcode table.  */

static const CGEN_OPCODE nds32_cgen_macro_insn_opcode_table[] =
{
/* neg $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_neg, { 0x52000000 }
  },
/* zeb $rt5,$ra5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), 0 } },
    & ifmt_zeb, { 0x540000ff }
  },
/* lbi $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lbi2, { 0x0 }
  },
/* lbi.p $rt5,[$ra5],$slo15b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15B), 0 } },
    & ifmt_lbi_p, { 0x8000000 }
  },
/* lb $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_lb1, { 0x38000000 }
  },
/* lb $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_lb2, { 0x38000000 }
  },
/* lb $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lb3, { 0x0 }
  },
/* lb.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lb_bi2, { 0x38000004 }
  },
/* lb.p $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lb_p, { 0x38000004 }
  },
/* lb.p $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lb_p2, { 0x38000004 }
  },
/* lhi $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lhi2, { 0x2000000 }
  },
/* lhi.p $rt5,[$ra5],$slo15h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15H), 0 } },
    & ifmt_lhi_p, { 0xa000000 }
  },
/* lh $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_lh1, { 0x38000001 }
  },
/* lh $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_lh2, { 0x38000001 }
  },
/* lh $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lh3, { 0x2000000 }
  },
/* lh.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lh_bi2, { 0x38000005 }
  },
/* lh.p $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lh_p, { 0x38000005 }
  },
/* lh.p $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lh_p2, { 0x38000005 }
  },
/* lwi $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lwi2, { 0x4000000 }
  },
/* lwi.p $rt5,[$ra5],$slo15w */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15W), 0 } },
    & ifmt_lwi_p, { 0xc000000 }
  },
/* lw $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_lw1, { 0x38000002 }
  },
/* lw $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_lw2, { 0x38000002 }
  },
/* lw $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lw3, { 0x4000000 }
  },
/* lw.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lw_bi2, { 0x38000006 }
  },
/* lw.p $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lw_p, { 0x38000006 }
  },
/* lw.p $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lw_p2, { 0x38000006 }
  },
/* lwup $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_lwup1, { 0x38000022 }
  },
/* lwup $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_lwup2, { 0x38000022 }
  },
/* swup $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_swup1, { 0x3800002a }
  },
/* swup $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_swup2, { 0x3800002a }
  },
/* lbsi $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lbsi2, { 0x20000000 }
  },
/* lbsi.p $rt5,[$ra5],$slo15b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15B), 0 } },
    & ifmt_lbsi_p, { 0x28000000 }
  },
/* lbs $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_lbs1, { 0x38000010 }
  },
/* lbs $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_lbs2, { 0x38000010 }
  },
/* lbs $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lbs3, { 0x20000000 }
  },
/* lbs.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lbs_bi2, { 0x38000014 }
  },
/* lbs.p $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lbs_p, { 0x38000014 }
  },
/* lbs.p $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lbs_p2, { 0x38000014 }
  },
/* lhsi $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lhsi2, { 0x22000000 }
  },
/* lhsi.p $rt5,[$ra5],$slo15h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15H), 0 } },
    & ifmt_lhsi_p, { 0x2a000000 }
  },
/* lhs $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_lhs1, { 0x38000011 }
  },
/* lhs $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_lhs2, { 0x38000011 }
  },
/* lhs $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_lhs3, { 0x22000000 }
  },
/* lhs.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lhs_bi2, { 0x38000015 }
  },
/* lhs.p $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_lhs_p, { 0x38000015 }
  },
/* lhs.p $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lhs_p2, { 0x38000015 }
  },
/* sbi $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_sbi2, { 0x10000000 }
  },
/* sbi.p $rt5,[$ra5],$slo15b */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15B), 0 } },
    & ifmt_sbi_p, { 0x18000000 }
  },
/* sb $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_sb1, { 0x38000008 }
  },
/* sb $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_sb2, { 0x38000008 }
  },
/* sb $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_sb3, { 0x10000000 }
  },
/* sb.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_sb_bi2, { 0x3800000c }
  },
/* sb.p $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_sb_p, { 0x3800000c }
  },
/* sb.p $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_sb_p2, { 0x3800000c }
  },
/* shi $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_shi2, { 0x12000000 }
  },
/* shi.p $rt5,[$ra5],$slo15h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15H), 0 } },
    & ifmt_shi_p, { 0x1a000000 }
  },
/* sh $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_sh1, { 0x38000009 }
  },
/* sh $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_sh2, { 0x38000009 }
  },
/* sh $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_sh3, { 0x12000000 }
  },
/* sh.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_sh_bi2, { 0x3800000d }
  },
/* sh.p $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_sh_p, { 0x3800000d }
  },
/* sh.p $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_sh_p2, { 0x3800000d }
  },
/* swi $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_swi2, { 0x14000000 }
  },
/* swi.p $rt5,[$ra5],$slo15w */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (SLO15W), 0 } },
    & ifmt_swi_p, { 0x1c000000 }
  },
/* sw $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_sw1, { 0x3800000a }
  },
/* sw $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_sw2, { 0x3800000a }
  },
/* sw $rt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_sw3, { 0x14000000 }
  },
/* sw.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_sw_bi2, { 0x3800000e }
  },
/* sw.p $rt5,[$ra5],$rb5<<$si */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), '<', '<', OP (SI), 0 } },
    & ifmt_sw_p, { 0x3800000e }
  },
/* sw.p $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_sw_p2, { 0x3800000e }
  },
/* lmw.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmw_bi2, { 0x3a000000 }
  },
/* lmw.bim $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmw_bim2, { 0x3a000004 }
  },
/* lmw.bd $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmw_bd2, { 0x3a000008 }
  },
/* lmw.bdm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmw_bdm2, { 0x3a00000c }
  },
/* lmw.ai $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmw_ai2, { 0x3a000010 }
  },
/* lmw.aim $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmw_aim2, { 0x3a000014 }
  },
/* lmw.ad $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmw_ad2, { 0x3a000018 }
  },
/* lmw.adm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmw_adm2, { 0x3a00001c }
  },
/* smw.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smw_bi2, { 0x3a000020 }
  },
/* smw.bim $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smw_bim2, { 0x3a000024 }
  },
/* smw.bd $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smw_bd2, { 0x3a000028 }
  },
/* smw.bdm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smw_bdm2, { 0x3a00002c }
  },
/* smw.ai $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smw_ai2, { 0x3a000030 }
  },
/* smw.aim $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smw_aim2, { 0x3a000034 }
  },
/* smw.ad $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smw_ad2, { 0x3a000038 }
  },
/* smw.adm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smw_adm2, { 0x3a00003c }
  },
/* llw $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_llw1, { 0x38000018 }
  },
/* llw $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_llw2, { 0x38000018 }
  },
/* scw $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_scw1, { 0x38000019 }
  },
/* scw $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_scw2, { 0x38000019 }
  },
/* ret */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_ret2, { 0x4a007820 }
  },
/* jral $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jral2, { 0x4be00001 }
  },
/* jral.iton $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jral_iton2, { 0x4be00101 }
  },
/* jral.ton $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jral_ton2, { 0x4be00301 }
  },
/* mfsr $rt5,$uimm_sr10 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (UIMM_SR10), 0 } },
    & ifmt_mfsr_alias, { 0x64000002 }
  },
/* mtsr $rt5,$uimm_sr10 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (UIMM_SR10), 0 } },
    & ifmt_mtsr_alias, { 0x64000003 }
  },
/* dprefi.d $dprefst,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DPREFST), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_dprefi_d2, { 0x27000000 }
  },
/* dprefi.w $dprefst,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DPREFST), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_dprefi_w2, { 0x26000000 }
  },
/* dpref $dprefst,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DPREFST), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_dpref1, { 0x38000013 }
  },
/* dpref $dprefst,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DPREFST), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_dpref2, { 0x38000013 }
  },
/* dpref $dprefst,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DPREFST), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_dpref3, { 0x26000000 }
  },
/* msync */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_msync2, { 0x6400000c }
  },
/* trap */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_trap2, { 0x64000005 }
  },
/* teqz $rt5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), 0 } },
    & ifmt_teqz2, { 0x64000006 }
  },
/* tnez $rt5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), 0 } },
    & ifmt_tnez2, { 0x64000007 }
  },
/* break */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_break2, { 0x6400000a }
  },
/* tlbop $ra5,$tlbopst */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RA5), ',', OP (TLBOPST), 0 } },
    & ifmt_tlbop2, { 0x6400000e }
  },
/* tlbop $tlbopst */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (TLBOPST), 0 } },
    & ifmt_tlbop3, { 0x6400000e }
  },
/* cctl $rt5,$ra5,$cctlst */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (CCTLST), 0 } },
    & ifmt_cctl1, { 0x64000001 }
  },
/* cctl $ra5,$cctlst */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RA5), ',', OP (CCTLST), 0 } },
    & ifmt_cctl2, { 0x64000001 }
  },
/* cctl $cctlst */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (CCTLST), 0 } },
    & ifmt_cctl3, { 0x64000001 }
  },
/* cctl $ra5,$cctlst,$cctllvl */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RA5), ',', OP (CCTLST), ',', OP (CCTLLVL), 0 } },
    & ifmt_cctl4, { 0x64000001 }
  },
/* nop */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_nop, { 0x40000009 }
  },
/* lwi333 $rt3_7,[$ra3] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), ']', 0 } },
    & ifmt_lwi3332, { 0xa000 }
  },
/* lhi333 $rt3_7,[$ra3] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), ']', 0 } },
    & ifmt_lhi3332, { 0xa400 }
  },
/* lbi333 $rt3_7,[$ra3] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), ']', 0 } },
    & ifmt_lbi3332, { 0xa600 }
  },
/* swi333 $rt3_7,[$ra3] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), ']', 0 } },
    & ifmt_swi3332, { 0xa800 }
  },
/* shi333 $rt3_7,[$ra3] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), ']', 0 } },
    & ifmt_shi3332, { 0xac00 }
  },
/* sbi333 $rt3_7,[$ra3] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3_7), ',', '[', OP (RA3), ']', 0 } },
    & ifmt_sbi3332, { 0xae00 }
  },
/* lwi37 $rt3,[\$fp] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', '[', '$', 'f', 'p', ']', 0 } },
    & ifmt_lwi372, { 0xb800 }
  },
/* swi37 $rt3,[\$fp] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', '[', '$', 'f', 'p', ']', 0 } },
    & ifmt_swi372, { 0xb880 }
  },
/* ret5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_ret52, { 0xdd9e }
  },
/* nop16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_nop16, { 0x9200 }
  },
/* lmwa.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwa_bi2, { 0x3a000001 }
  },
/* lmwa.bim $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwa_bim2, { 0x3a000005 }
  },
/* lmwa.bd $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwa_bd2, { 0x3a000009 }
  },
/* lmwa.bdm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwa_bdm2, { 0x3a00000d }
  },
/* lmwa.ai $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwa_ai2, { 0x3a000011 }
  },
/* lmwa.aim $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwa_aim2, { 0x3a000015 }
  },
/* lmwa.ad $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwa_ad2, { 0x3a000019 }
  },
/* lmwa.adm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwa_adm2, { 0x3a00001d }
  },
/* smwa.bi $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwa_bi2, { 0x3a000021 }
  },
/* smwa.bim $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwa_bim2, { 0x3a000025 }
  },
/* smwa.bd $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwa_bd2, { 0x3a000029 }
  },
/* smwa.bdm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwa_bdm2, { 0x3a00002d }
  },
/* smwa.ai $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwa_ai2, { 0x3a000031 }
  },
/* smwa.aim $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwa_aim2, { 0x3a000035 }
  },
/* smwa.ad $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwa_ad2, { 0x3a000039 }
  },
/* smwa.adm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwa_adm2, { 0x3a00003d }
  },
/* lbup $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_lbup1, { 0x38000020 }
  },
/* lbup $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_lbup2, { 0x38000020 }
  },
/* sbup $rt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_sbup1, { 0x38000028 }
  },
/* sbup $rt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_sbup2, { 0x38000028 }
  },
/* lmwzb.b $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwzb_b2, { 0x3a000002 }
  },
/* lmwzb.bm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwzb_bm2, { 0x3a000006 }
  },
/* lmwzb.a $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwzb_a2, { 0x3a000012 }
  },
/* lmwzb.am $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_lmwzb_am2, { 0x3a000016 }
  },
/* smwzb.b $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwzb_b2, { 0x3a000022 }
  },
/* smwzb.bm $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwzb_bm2, { 0x3a000026 }
  },
/* smwzb.a $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwzb_a2, { 0x3a000032 }
  },
/* smwzb.am $rt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_smwzb_am2, { 0x3a000036 }
  },
/* jralnez $rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5), 0 } },
    & ifmt_jralnez2, { 0x4be00003 }
  },
/* cctl $cctlst,$cctllvl */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (CCTLST), ',', OP (CCTLLVL), 0 } },
    & ifmt_cctl5, { 0x64000001 }
  },
/* beq_r $rt5,$ra5,$disp14 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (DISP14), 0 } },
    & ifmt_beq_r, { 0x4c000000 }
  },
/* bne_r $rt5,$ra5,$disp14 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RA5), ',', OP (DISP14), 0 } },
    & ifmt_bne_r, { 0x4c004000 }
  },
/* beqz_r $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_beqz_r, { 0x4e020000 }
  },
/* bnez_r $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_bnez_r, { 0x4e030000 }
  },
/* bgez_r $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_bgez_r, { 0x4e040000 }
  },
/* bltz_r $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_bltz_r, { 0x4e050000 }
  },
/* bgtz_r $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_bgtz_r, { 0x4e060000 }
  },
/* blez_r $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_blez_r, { 0x4e070000 }
  },
/* beqs38_r $rt3,$hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', OP (HSDISP8), 0 } },
    & ifmt_beqs38_r, { 0xd000 }
  },
/* bnes38_r $rt3,$hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', OP (HSDISP8), 0 } },
    & ifmt_bnes38_r, { 0xd800 }
  },
/* beqz38_r $rt3,$hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', OP (HSDISP8), 0 } },
    & ifmt_beqz38_r, { 0xc000 }
  },
/* bnez38_r $rt3,$hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT3), ',', OP (HSDISP8), 0 } },
    & ifmt_bnez38_r, { 0xc800 }
  },
/* beqzs8_r $hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (HSDISP8), 0 } },
    & ifmt_beqzs8_r, { 0xe800 }
  },
/* bnezs8_r $hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (HSDISP8), 0 } },
    & ifmt_bnezs8_r, { 0xe900 }
  },
/* bgezal_r $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_bgezal_r, { 0x4e0c0000 }
  },
/* bltzal_r $rt5,$disp16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (DISP16), 0 } },
    & ifmt_bltzal_r, { 0x4e0d0000 }
  },
/* j_r $disp24 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DISP24), 0 } },
    & ifmt_j_r, { 0x48000000 }
  },
/* j8_r $hsdisp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (HSDISP8), 0 } },
    & ifmt_j8_r, { 0xd500 }
  },
/* jal_r $disp24 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (DISP24), 0 } },
    & ifmt_jal_r, { 0x49000000 }
  },
/* jral_r $rt5,$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (RB5), 0 } },
    & ifmt_jral_r, { 0x4a000001 }
  },
/* jral5_r $rb5h */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RB5H), 0 } },
    & ifmt_jral5_r, { 0xdd20 }
  },
/* beqc_r $rt5,$simm11,$disp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (SIMM11), ',', OP (DISP8), 0 } },
    & ifmt_beqc_r, { 0x5a000000 }
  },
/* bnec_r $rt5,$simm11,$disp8 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (RT5), ',', OP (SIMM11), ',', OP (DISP8), 0 } },
    & ifmt_bnec_r, { 0x5a080000 }
  },
/* fls $fsrt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_fls1, { 0x6a000002 }
  },
/* fls $fsrt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_fls2, { 0x6a000002 }
  },
/* fls.bi $fsrt5,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_fls1_bi, { 0x6a000082 }
  },
/* fls.bi $fsrt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_fls2_bi, { 0x6a000082 }
  },
/* flsi $fsrt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_flsi1, { 0x30000000 }
  },
/* flsi1.bi $fsrt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_flsi1_bi, { 0x30001000 }
  },
/* fss $fsrt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_fss1, { 0x6a00000a }
  },
/* fss $fsrt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_fss2, { 0x6a00000a }
  },
/* fss.bi $fsrt5,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_fss_bi1, { 0x6a00008a }
  },
/* fss.bi $fsrt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FSRT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_fss_bi2, { 0x6a00008a }
  },
/* fld $fdrt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_fld1, { 0x6a000003 }
  },
/* fld $fdrt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_fld2, { 0x6a000003 }
  },
/* fld.bi $fdrt5,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_fld1_bi, { 0x6a000083 }
  },
/* fld.bi $fdrt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_fld2_bi, { 0x6a000083 }
  },
/* fldi $fdrt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_fldi1, { 0x34000000 }
  },
/* fldi.bi $fdrt5,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_fldi1_bi, { 0x34001000 }
  },
/* fsd $fdrt5,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_fsd1, { 0x6a00000b }
  },
/* fsd $fdrt5,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_fsd2, { 0x6a00000b }
  },
/* fsd.bi $fdrt5,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_fsd1_bi, { 0x6a00008b }
  },
/* fsd.bi $fdrt5,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (FDRT5), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_fsd2_bi, { 0x6a00008b }
  },
/* cpld cp1,$copdr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpld_cp1_1, { 0x6a000013 }
  },
/* cpld cp1,$copdr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpld_cp1_2, { 0x6a000013 }
  },
/* cpld cp1,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpld_cp1_3, { 0x6a000013 }
  },
/* cpld.bi cp1,$copdr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpld_bi_cp1_1, { 0x6a000093 }
  },
/* cpld.bi cp1,$copdr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpld_bi_cp1_2, { 0x6a000093 }
  },
/* cpld.bi cp1,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpld_bi_cp1_3, { 0x6a000093 }
  },
/* cpldi cp1,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpldi_cp1_1, { 0x34002000 }
  },
/* cpldi.bi cp1,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpldi_bi_cp1_1, { 0x34003000 }
  },
/* cpld cp2,$copdr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpld_cp2_1, { 0x6a000023 }
  },
/* cpld cp2,$copdr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpld_cp2_2, { 0x6a000023 }
  },
/* cpld cp2,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpld_cp2_3, { 0x6a000023 }
  },
/* cpld.bi cp2,$copdr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpld_bi_cp2_1, { 0x6a0000a3 }
  },
/* cpld.bi cp2,$copdr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpld_bi_cp2_2, { 0x6a0000a3 }
  },
/* cpld.bi cp2,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpld_bi_cp2_3, { 0x6a0000a3 }
  },
/* cpldi cp2,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpldi_cp2_1, { 0x34004000 }
  },
/* cpldi.bi cp2,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpldi_bi_cp2_1, { 0x34005000 }
  },
/* cpld cp3,$copdr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpld_cp3_1, { 0x6a000033 }
  },
/* cpld cp3,$copdr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpld_cp3_2, { 0x6a000033 }
  },
/* cpld cp3,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpld_cp3_3, { 0x6a000033 }
  },
/* cpld.bi cp3,$copdr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpld_bi_cp3_1, { 0x6a0000b3 }
  },
/* cpld.bi cp3,$copdr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpld_bi_cp3_2, { 0x6a0000b3 }
  },
/* cpld.bi cp3,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpld_bi_cp3_3, { 0x6a0000b3 }
  },
/* cpldi cp3,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpldi_cp3_1, { 0x34006000 }
  },
/* cpldi.bi cp3,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpldi_bi_cp3_1, { 0x34007000 }
  },
/* cplw cp1,$copwr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cplw_cp1_1, { 0x6a000012 }
  },
/* cplw cp1,$copwr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cplw_cp1_2, { 0x6a000012 }
  },
/* cplw cp1,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplw_cp1_3, { 0x6a000012 }
  },
/* cplw.bi cp1,$copwr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cplw_bi_cp1_1, { 0x6a000092 }
  },
/* cplw.bi cp1,$copwr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cplw_bi_cp1_2, { 0x6a000092 }
  },
/* cplw.bi cp1,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplw_bi_cp1_3, { 0x6a000092 }
  },
/* cplwi cp1,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplwi_cp1_1, { 0x30002000 }
  },
/* cplwi.bi cp1,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplwi_bi_cp1_1, { 0x30003000 }
  },
/* cplw cp2,$copwr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cplw_cp2_1, { 0x6a000022 }
  },
/* cplw cp2,$copwr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cplw_cp2_2, { 0x6a000022 }
  },
/* cplw cp2,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplw_cp2_3, { 0x6a000022 }
  },
/* cplw.bi cp2,$copwr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cplw_bi_cp2_1, { 0x6a0000a2 }
  },
/* cplw.bi cp2,$copwr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cplw_bi_cp2_2, { 0x6a0000a2 }
  },
/* cplw.bi cp2,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplw_bi_cp2_3, { 0x6a0000a2 }
  },
/* cplwi cp2,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplwi_cp2_1, { 0x30004000 }
  },
/* cplwi.bi cp2,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplwi_bi_cp2_1, { 0x30005000 }
  },
/* cplw cp3,$copwr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cplw_cp3_1, { 0x6a000032 }
  },
/* cplw cp3,$copwr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cplw_cp3_2, { 0x6a000032 }
  },
/* cplw cp3,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplw_cp3_3, { 0x6a000032 }
  },
/* cplw.bi cp3,$copwr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cplw_bi_cp3_1, { 0x6a0000b2 }
  },
/* cplw.bi cp3,$copwr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cplw_bi_cp3_2, { 0x6a0000b2 }
  },
/* cplw.bi cp3,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplw_bi_cp3_3, { 0x6a0000b2 }
  },
/* cplwi cp3,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplwi_cp3_1, { 0x30006000 }
  },
/* cplwi.bi cp3,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cplwi_bi_cp3_1, { 0x30007000 }
  },
/* cpsd cp1,$copdr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpsd_cp1_1, { 0x6a00001b }
  },
/* cpsd cp1,$copdr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpsd_cp1_2, { 0x6a00001b }
  },
/* cpsd cp1,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsd_cp1_3, { 0x6a00001b }
  },
/* cpsd.bi cp1,$copdr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpsd_bi_cp1_1, { 0x6a00009b }
  },
/* cpsd.bi cp1,$copdr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpsd_bi_cp1_2, { 0x6a00009b }
  },
/* cpsd.bi cp1,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsd_bi_cp1_3, { 0x6a00009b }
  },
/* cpsdi cp1,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsdi_cp1_1, { 0x36002000 }
  },
/* cpsdi.bi cp1,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsdi_bi_cp1_1, { 0x36003000 }
  },
/* cpsd cp2,$copdr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpsd_cp2_1, { 0x6a00002b }
  },
/* cpsd cp2,$copdr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpsd_cp2_2, { 0x6a00002b }
  },
/* cpsd cp2,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsd_cp2_3, { 0x6a00002b }
  },
/* cpsd.bi cp2,$copdr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpsd_bi_cp2_1, { 0x6a0000ab }
  },
/* cpsd.bi cp2,$copdr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpsd_bi_cp2_2, { 0x6a0000ab }
  },
/* cpsd.bi cp2,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsd_bi_cp2_3, { 0x6a0000ab }
  },
/* cpsdi cp2,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsdi_cp2_1, { 0x36004000 }
  },
/* cpsdi.bi cp2,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsdi_bi_cp2_1, { 0x36005000 }
  },
/* cpsd cp3,$copdr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpsd_cp3_1, { 0x6a00003b }
  },
/* cpsd cp3,$copdr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpsd_cp3_2, { 0x6a00003b }
  },
/* cpsd cp3,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsd_cp3_3, { 0x6a00003b }
  },
/* cpsd.bi cp3,$copdr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpsd_bi_cp3_1, { 0x6a0000bb }
  },
/* cpsd.bi cp3,$copdr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpsd_bi_cp3_2, { 0x6a0000bb }
  },
/* cpsd.bi cp3,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsd_bi_cp3_3, { 0x6a0000bb }
  },
/* cpsdi cp3,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsdi_cp3_1, { 0x36006000 }
  },
/* cpsdi.bi cp3,$copdr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPDR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsdi_bi_cp3_1, { 0x36007000 }
  },
/* cpsw cp1,$copwr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpsw_cp1_1, { 0x6a00001a }
  },
/* cpsw cp1,$copwr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpsw_cp1_2, { 0x6a00001a }
  },
/* cpsw cp1,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsw_cp1_3, { 0x6a00001a }
  },
/* cpsw.bi cp1,$copwr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpsw_bi_cp1_1, { 0x6a00009a }
  },
/* cpsw.bi cp1,$copwr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpsw_bi_cp1_2, { 0x6a00009a }
  },
/* cpsw.bi cp1,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsw_bi_cp1_3, { 0x6a00009a }
  },
/* cpswi cp1,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpswi_cp1_1, { 0x32002000 }
  },
/* cpswi.bi cp1,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '1', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpswi_bi_cp1_1, { 0x32003000 }
  },
/* cpsw cp2,$copwr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpsw_cp2_1, { 0x6a00002a }
  },
/* cpsw cp2,$copwr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpsw_cp2_2, { 0x6a00002a }
  },
/* cpsw cp2,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsw_cp2_3, { 0x6a00002a }
  },
/* cpsw.bi cp2,$copwr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpsw_bi_cp2_1, { 0x6a0000aa }
  },
/* cpsw.bi cp2,$copwr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpsw_bi_cp2_2, { 0x6a0000aa }
  },
/* cpsw.bi cp2,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsw_bi_cp2_3, { 0x6a0000aa }
  },
/* cpswi cp2,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpswi_cp2_1, { 0x32004000 }
  },
/* cpswi.bi cp2,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '2', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpswi_bi_cp2_1, { 0x32005000 }
  },
/* cpsw cp3,$copwr,[$ra5+($rb5<<$si)] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), '+', '(', OP (RB5), '<', '<', OP (SI), ')', ']', 0 } },
    & ifmt_cpsw_cp3_1, { 0x6a00003a }
  },
/* cpsw cp3,$copwr,[$ra5+$rb5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), '+', OP (RB5), ']', 0 } },
    & ifmt_cpsw_cp3_2, { 0x6a00003a }
  },
/* cpsw cp3,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsw_cp3_3, { 0x6a00003a }
  },
/* cpsw.bi cp3,$copwr,[$ra5],($rb5<<$si) */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', '(', OP (RB5), '<', '<', OP (SI), ')', 0 } },
    & ifmt_cpsw_bi_cp3_1, { 0x6a0000ba }
  },
/* cpsw.bi cp3,$copwr,[$ra5],$rb5 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', ',', OP (RB5), 0 } },
    & ifmt_cpsw_bi_cp3_2, { 0x6a0000ba }
  },
/* cpsw.bi cp3,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpsw_bi_cp3_3, { 0x6a0000ba }
  },
/* cpswi cp3,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpswi_cp3_1, { 0x32006000 }
  },
/* cpswi.bi cp3,$copwr,[$ra5] */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', 'c', 'p', '3', ',', OP (COPWR), ',', '[', OP (RA5), ']', 0 } },
    & ifmt_cpswi_bi_cp3_1, { 0x32007000 }
  },
/* ifret16 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, 0 } },
    & ifmt_ifret16, { 0x83ff }
  },
/* j.it $concat24 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (CONCAT24), 0 } },
    & ifmt_j_it, { 0x48000000 }
  },
/* jal.it $concat24 */
  {
    { 0, 0, 0, 0 },
    { { MNEM, ' ', OP (CONCAT24), 0 } },
    & ifmt_jal_it, { 0x49000000 }
  },
};

#undef A
#undef OPERAND
#undef MNEM
#undef OP

#ifndef CGEN_ASM_HASH_P
#define CGEN_ASM_HASH_P(insn) 1
#endif

#ifndef CGEN_DIS_HASH_P
#define CGEN_DIS_HASH_P(insn) 1
#endif

/* Return non-zero if INSN is to be added to the hash table.
   Targets are free to override CGEN_{ASM,DIS}_HASH_P in the .opc file.  */

static int
asm_hash_insn_p (insn)
     const CGEN_INSN *insn ATTRIBUTE_UNUSED;
{
  return CGEN_ASM_HASH_P (insn);
}

static int
dis_hash_insn_p (insn)
     const CGEN_INSN *insn;
{
  /* If building the hash table and the NO-DIS attribute is present,
     ignore.  */
  if (CGEN_INSN_ATTR_VALUE (insn, CGEN_INSN_NO_DIS))
    return 0;
  return CGEN_DIS_HASH_P (insn);
}

#ifndef CGEN_ASM_HASH
#define CGEN_ASM_HASH_SIZE 127
#ifdef CGEN_MNEMONIC_OPERANDS
#define CGEN_ASM_HASH(mnem) (*(unsigned char *) (mnem) % CGEN_ASM_HASH_SIZE)
#else
#define CGEN_ASM_HASH(mnem) (*(unsigned char *) (mnem) % CGEN_ASM_HASH_SIZE) /*FIXME*/
#endif
#endif

/* It doesn't make much sense to provide a default here,
   but while this is under development we do.
   BUFFER is a pointer to the bytes of the insn, target order.
   VALUE is the first base_insn_bitsize bits as an int in host order.  */

#ifndef CGEN_DIS_HASH
#define CGEN_DIS_HASH_SIZE 256
#define CGEN_DIS_HASH(buf, value) (*(unsigned char *) (buf))
#endif

/* The result is the hash value of the insn.
   Targets are free to override CGEN_{ASM,DIS}_HASH in the .opc file.  */

static unsigned int
asm_hash_insn (mnem)
     const char * mnem;
{
  return CGEN_ASM_HASH (mnem);
}

/* BUF is a pointer to the bytes of the insn, target order.
   VALUE is the first base_insn_bitsize bits as an int in host order.  */

static unsigned int
dis_hash_insn (buf, value)
     const char * buf ATTRIBUTE_UNUSED;
     CGEN_INSN_INT value ATTRIBUTE_UNUSED;
{
  return CGEN_DIS_HASH (buf, value);
}

/* Set the recorded length of the insn in the CGEN_FIELDS struct.  */

static void
set_fields_bitsize (CGEN_FIELDS *fields, int size)
{
  CGEN_FIELDS_BITSIZE (fields) = size;
}

/* Function to call before using the operand instance table.
   This plugs the opcode entries and macro instructions into the cpu table.  */

void
nds32_cgen_init_opcode_table (CGEN_CPU_DESC cd)
{
  int i;
  int num_macros = (sizeof (nds32_cgen_macro_insn_table) /
		    sizeof (nds32_cgen_macro_insn_table[0]));
  const CGEN_IBASE *ib = & nds32_cgen_macro_insn_table[0];
  const CGEN_OPCODE *oc = & nds32_cgen_macro_insn_opcode_table[0];
  CGEN_INSN *insns = xmalloc (num_macros * sizeof (CGEN_INSN));

  /* This test has been added to avoid a warning generated
     if memset is called with a third argument of value zero.  */
  if (num_macros >= 1)
    memset (insns, 0, num_macros * sizeof (CGEN_INSN));
  for (i = 0; i < num_macros; ++i)
    {
      insns[i].base = &ib[i];
      insns[i].opcode = &oc[i];
      nds32_cgen_build_insn_regex (& insns[i]);
    }
  cd->macro_insn_table.init_entries = insns;
  cd->macro_insn_table.entry_size = sizeof (CGEN_IBASE);
  cd->macro_insn_table.num_init_entries = num_macros;

  oc = & nds32_cgen_insn_opcode_table[0];
  insns = (CGEN_INSN *) cd->insn_table.init_entries;
  for (i = 0; i < MAX_INSNS; ++i)
    {
      insns[i].opcode = &oc[i];
      nds32_cgen_build_insn_regex (& insns[i]);
    }

  cd->sizeof_fields = sizeof (CGEN_FIELDS);
  cd->set_fields_bitsize = set_fields_bitsize;

  cd->asm_hash_p = asm_hash_insn_p;
  cd->asm_hash = asm_hash_insn;
  cd->asm_hash_size = CGEN_ASM_HASH_SIZE;

  cd->dis_hash_p = dis_hash_insn_p;
  cd->dis_hash = dis_hash_insn;
  cd->dis_hash_size = CGEN_DIS_HASH_SIZE;
}
