/* CPU data header for nds32.

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

#ifndef NDS32_CPU_H
#define NDS32_CPU_H

#define CGEN_ARCH nds32

/* Given symbol S, return nds32_cgen_<S>.  */
#define CGEN_SYM(s) nds32##_cgen_##s


/* Selected cpu families.  */
#define HAVE_CPU_NDS32HF

#define CGEN_INSN_LSB0_P 0

/* Minimum size of any insn (in bytes).  */
#define CGEN_MIN_INSN_SIZE 2

/* Maximum size of any insn (in bytes).  */
#define CGEN_MAX_INSN_SIZE 4

#define CGEN_INT_INSN_P 1

/* Maximum number of syntax elements in an instruction.  */
#define CGEN_ACTUAL_MAX_SYNTAX_ELEMENTS 34

/* CGEN_MNEMONIC_OPERANDS is defined if mnemonics have operands.
   e.g. In "b,a foo" the ",a" is an operand.  If mnemonics have operands
   we can't hash on everything up to the space.  */
#define CGEN_MNEMONIC_OPERANDS

/* Maximum number of fields in an instruction.  */
#define CGEN_ACTUAL_MAX_IFMT_OPERANDS 15

/* Enums.  */

/* Enum declaration for insn format (32/16) enums.  */
typedef enum insn_format {
  IFMT_32, IFMT_16
} INSN_FORMAT;

/* Enum declaration for insn opcode group enums.  */
typedef enum insn32_opc6g {
  OPC6G_0, OPC6G_1, OPC6G_2, OPC6G_3
 , OPC6G_4, OPC6G_5, OPC6G_6, OPC6G_7
} INSN32_OPC6G;

/* Enum declaration for  insn opcode group 0enums.  */
typedef enum insn32_opc6c0 {
  OPC6C0_LBI, OPC6C0_LHI, OPC6C0_LWI, OPC6C0_LDI
 , OPC6C0_LBIP, OPC6C0_LHIP, OPC6C0_LWIP, OPC6C0_LDIP
} INSN32_OPC6C0;

/* Enum declaration for  insn opcode group 1enums.  */
typedef enum insn32_opc6c1 {
  OPC6C1_SBI, OPC6C1_SHI, OPC6C1_SWI, OPC6C1_SDI
 , OPC6C1_SBIP, OPC6C1_SHIP, OPC6C1_SWIP, OPC6C1_SDIP
} INSN32_OPC6C1;

/* Enum declaration for  insn opcode group 2enums.  */
typedef enum insn32_opc6c2 {
  OPC6C2_LBSI, OPC6C2_LHSI, OPC6C2_LWSI, OPC6C2_DPREFI
 , OPC6C2_LBSIP, OPC6C2_LHSIP, OPC6C2_LWSIP, OPC6C2_LBGP
} INSN32_OPC6C2;

/* Enum declaration for  insn opcode group 3enums.  */
typedef enum insn32_opc6c3 {
  OPC6C3_LWC, OPC6C3_SWC, OPC6C3_LDC, OPC6C3_SDC
 , OPC6C3_MEM, OPC6C3_LSMW, OPC6C3_HWGP, OPC6C3_SBGP
} INSN32_OPC6C3;

/* Enum declaration for  insn opcode group 4enums.  */
typedef enum insn32_opc6c4 {
  OPC6C4_ALU_1, OPC6C4_ALU_2, OPC6C4_MOVI, OPC6C4_SETHI
 , OPC6C4_JI, OPC6C4_JR, OPC6C4_BR1, OPC6C4_BR2
} INSN32_OPC6C4;

/* Enum declaration for  insn opcode group 5enums.  */
typedef enum insn32_opc6c5 {
  OPC6C5_ADDI, OPC6C5_SUBRI, OPC6C5_ANDI, OPC6C5_XORI
 , OPC6C5_ORI, OPC6C5_BR3, OPC6C5_SLTI, OPC6C5_SLTSI
} INSN32_OPC6C5;

/* Enum declaration for  insn opcode group 6enums.  */
typedef enum insn32_opc6c6 {
  OPC6C6_AEXT, OPC6C6_CEXT, OPC6C6_MISC, OPC6C6_BITCI
 , OPC6C6_4, OPC6C6_COP, OPC6C6_6, OPC6C6_7
} INSN32_OPC6C6;

/* Enum declaration for  insn opcode group 7enums.  */
typedef enum insn32_opc6c7 {
  OPC6C7_SIMD, OPC6C7_1, OPC6C7_2, OPC6C7_3
 , OPC6C7_4, OPC6C7_5, OPC6C7_6, OPC6C7_7
} INSN32_OPC6C7;

/* Enum declaration for insn type 0 1-bit subcode enums.  */
typedef enum ji_1_sub1 {
  JI_SUB1_J, JI_SUB1_JAL
} JI_1_SUB1;

/* Enum declaration for 1-bit subcode enums for dpref/dprefi.  */
typedef enum dpref_sub1 {
  DPREF_SUB1_W, DPREF_SUB1_D
} DPREF_SUB1;

/* Enum declaration for insn type 2 1-bit subcode enums.  */
typedef enum br_1_sub1 {
  BR1_SUB1_BEQ, BR1_SUB1_BNE
} BR_1_SUB1;

/* Enum declaration for insn type 1 4-bit subcode enums.  */
typedef enum br_2_sub4 {
  BR2_SUB4_IFCALL, BR2_SUB4_1, BR2_SUB4_BEQZ, BR2_SUB4_BNEZ
 , BR2_SUB4_BGEZ, BR2_SUB4_BLTZ, BR2_SUB4_BGTZ, BR2_SUB4_BLEZ
 , BR2_SUB4_8, BR2_SUB4_9, BR2_SUB4_10, BR2_SUB4_BNEZD
 , BR2_SUB4_BGEZAL, BR2_SUB4_BLTZAL, BR2_SUB4_14, BR2_SUB4_15
} BR_2_SUB4;

/* Enum declaration for insn type 3 10-bit reserved field enums.  */
typedef enum insn32_res10_7 {
  RES10_7_0
} INSN32_RES10_7;

/* Enum declaration for insn type 3 10-bit reserved field enums.  */
typedef enum insn32_res10_12 {
  RES10_12_0
} INSN32_RES10_12;

/* Enum declaration for insn type 3 12-bit reserved field enums.  */
typedef enum insn32_res12_12 {
  RES12_12_0
} INSN32_RES12_12;

/* Enum declaration for enums for interruption register of SRs.  */
typedef enum sr10_ir {
  SR10_IR_PSW = 128
} SR10_IR;

/* Enum declaration for insn type 3 15-bit reserved field enums.  */
typedef enum insn32_res15 {
  RES15_0
} INSN32_RES15;

/* Enum declaration for 3-bit reserved field enums.  */
typedef enum insn32_res3_22 {
  RES3_22_0
} INSN32_RES3_22;

/* Enum declaration for 5-bit reserved field enums.  */
typedef enum insn32_res5_7 {
  RES5_7_0
} INSN32_RES5_7;

/* Enum declaration for 5-bit reserved field enums.  */
typedef enum insn32_res5_12 {
  RES5_12_0
} INSN32_RES5_12;

/* Enum declaration for 5-bit reserved field enums.  */
typedef enum insn32_res5_17 {
  RES5_17_0
} INSN32_RES5_17;

/* Enum declaration for 4-bit reserved field enums.  */
typedef enum insn32_res4_17 {
  RES4_17_0
} INSN32_RES4_17;

/* Enum declaration for insn type 5 2-bit reserved field enums.  */
typedef enum insn32_res2 {
  RES2_30_0, RES2_30_1, RES2_30_2, RES2_30_3
} INSN32_RES2;

/* Enum declaration for insn type 3 10-bit subcode domain enums for load/store.  */
typedef enum insn32_sub10dsi {
  SUB10DSI_0
} INSN32_SUB10DSI;

/* Enum declaration for insn type 3 10-bit subcode domain enums.  */
typedef enum insn32_sub10d {
  SUB10D_0 = 0, SUB10D_1 = 1, SUB10D_2 = 2, SUB10D_3 = 3
 , SUB10D_4 = 4, SUB10D_5 = 5, SUB10D_6 = 6, SUB10D_7 = 7
 , SUB10D_8 = 8, SUB10D_9 = 9, SUB10D_10 = 10, SUB10D_11 = 11
 , SUB10D_12 = 12, SUB10D_13 = 13, SUB10D_14 = 14, SUB10D_15 = 15
 , SUB10D_NO_IDT = 0, SUB10D_IT = 4, SUB10D_DT = 8, SUB10D_IDT = 12
 , SUB10D_T = 12
} INSN32_SUB10D;

/* Enum declaration for insn type 3 10-bit subcode group enums.  */
typedef enum insn32_sub10g {
  SUB10G_0 = 0, SUB10G_1 = 1, SUB10G_2 = 2, SUB10G_3 = 3
 , SUB10G_4 = 4, SUB10G_5 = 5, SUB10G_6 = 6, SUB10G_7 = 7
 , SUB10G_JR = 0, SUB10G_RET = 4, SUB10G_JRAL = 0
} INSN32_SUB10G;

/* Enum declaration for insn type 3 10-bit subcode group2 enums.  */
typedef enum insn32_sub10g2 {
  SUB10G2_0, SUB10G2_1, SUB10G2_2, SUB10G2_3
} INSN32_SUB10G2;

/* Enum declaration for ALU_1 subcode group 0enums.  */
typedef enum alu_1_sub10c0 {
  ALU_1_SUB10C0_ADD, ALU_1_SUB10C0_SUB, ALU_1_SUB10C0_AND, ALU_1_SUB10C0_XOR
 , ALU_1_SUB10C0_OR, ALU_1_SUB10C0_NOR, ALU_1_SUB10C0_SLT, ALU_1_SUB10C0_SLTS
} ALU_1_SUB10C0;

/* Enum declaration for ALU_1 subcode group 1enums.  */
typedef enum alu_1_sub10c1 {
  ALU_1_SUB10C1_SLLI, ALU_1_SUB10C1_SRLI, ALU_1_SUB10C1_SRAI, ALU_1_SUB10C1_ROTRI
 , ALU_1_SUB10C1_SLL, ALU_1_SUB10C1_SRL, ALU_1_SUB10C1_SRA, ALU_1_SUB10C1_ROTR
} ALU_1_SUB10C1;

/* Enum declaration for ALU_1 subcode group 2enums.  */
typedef enum alu_1_sub10c2 {
  ALU_1_SUB10C2_SEB, ALU_1_SUB10C2_SEH, ALU_1_SUB10C2_BITC, ALU_1_SUB10C2_ZEH
 , ALU_1_SUB10C2_WSBH, ALU_1_SUB10C2_5, ALU_1_SUB10C2_DIVSR, ALU_1_SUB10C2_DIVR
} ALU_1_SUB10C2;

/* Enum declaration for ALU_1 subcode group 3enums.  */
typedef enum alu_1_sub10c3 {
  ALU_1_SUB10C3_SVA, ALU_1_SUB10C3_SVS, ALU_1_SUB10C3_CMOVZ, ALU_1_SUB10C3_CMOVN
 , ALU_1_SUB10C3_4, ALU_1_SUB10C3_5, ALU_1_SUB10C3_6, ALU_1_SUB10C3_7
} ALU_1_SUB10C3;

/* Enum declaration for ALU_2 subcode group 0enums.  */
typedef enum alu_2_sub10c0 {
  ALU_2_SUB10C0_MAX, ALU_2_SUB10C0_MIN, ALU_2_SUB10C0_AVE, ALU_2_SUB10C0_ABS
 , ALU_2_SUB10C0_CLIPS, ALU_2_SUB10C0_CLIP, ALU_2_SUB10C0_CLO, ALU_2_SUB10C0_CLZ
} ALU_2_SUB10C0;

/* Enum declaration for ALU_2 subcode group 1enums.  */
typedef enum alu_2_sub10c1 {
  ALU_2_SUB10C1_BSET, ALU_2_SUB10C1_BCLR, ALU_2_SUB10C1_BTGL, ALU_2_SUB10C1_BTST
 , ALU_2_SUB10C1_BSE, ALU_2_SUB10C1_BSP, ALU_2_SUB10C1_STR1, ALU_2_SUB10C1_STR2
} ALU_2_SUB10C1;

/* Enum declaration for ALU_2 subcode group 2enums.  */
typedef enum alu_2_sub10c2 {
  ALU_2_SUB10C2_0, ALU_2_SUB10C2_1, ALU_2_SUB10C2_ADDWC, ALU_2_SUB10C2_SUBWC
 , ALU_2_SUB10C2_KDMXY, ALU_2_SUB10C2_5, ALU_2_SUB10C2_6, ALU_2_SUB10C2_FFZMISM
} ALU_2_SUB10C2;

/* Enum declaration for ALU_2 subcode group 3enums.  */
typedef enum alu_2_sub10c3 {
  ALU_2_SUB10C3_KADDW, ALU_2_SUB10C3_KSUBW, ALU_2_SUB10C3_KSLRAW, ALU_2_SUB10C3_3
 , ALU_2_SUB10C3_4, ALU_2_SUB10C3_5, ALU_2_SUB10C3_6, ALU_2_SUB10C3_7
} ALU_2_SUB10C3;

/* Enum declaration for ALU_2 subcode group 4enums.  */
typedef enum alu_2_sub10c4 {
  ALU_2_SUB10C4_MFUSR, ALU_2_SUB10C4_MTUSR, ALU_2_SUB10C4_2, ALU_2_SUB10C4_3
 , ALU_2_SUB10C4_MUL, ALU_2_SUB10C4_5, ALU_2_SUB10C4_6, ALU_2_SUB10C4_7
} ALU_2_SUB10C4;

/* Enum declaration for ALU_2 subcode group 5enums.  */
typedef enum alu_2_sub10c5 {
  ALU_2_SUB10C5_MULTS64, ALU_2_SUB10C5_MULT64, ALU_2_SUB10C5_MADDS64, ALU_2_SUB10C5_MADD64
 , ALU_2_SUB10C5_MSUBS64, ALU_2_SUB10C5_MSUB64, ALU_2_SUB10C5_DIVS, ALU_2_SUB10C5_DIV
} ALU_2_SUB10C5;

/* Enum declaration for ALU_2 subcode group 6enums.  */
typedef enum alu_2_sub10c6 {
  ALU_2_SUB10C6_MULTS32, ALU_2_SUB10C6_MULT32, ALU_2_SUB10C6_MADDS32, ALU_2_SUB10C6_MADD32
 , ALU_2_SUB10C6_MSUBS32, ALU_2_SUB10C6_MSUB32, ALU_2_SUB10C6_6, ALU_2_SUB10C6_7
} ALU_2_SUB10C6;

/* Enum declaration for ALU_2 subcode group 7enums.  */
typedef enum alu_2_sub10c7 {
  ALU_2_SUB10C7_DMADD, ALU_2_SUB10C7_DMADDC, ALU_2_SUB10C7_DMSUB, ALU_2_SUB10C7_DMSUBC
 , ALU_2_SUB10C7_RMFHI, ALU_2_SUB10C7_QMFLO, ALU_2_SUB10C7_6, ALU_2_SUB10C7_7
} ALU_2_SUB10C7;

/* Enum declaration for MEM subcode group 0enums.  */
typedef enum mem_sub10c0 {
  MEM_SUB10C0_LB, MEM_SUB10C0_LH, MEM_SUB10C0_LW, MEM_SUB10C0_LD
 , MEM_SUB10C0_LBP, MEM_SUB10C0_LHP, MEM_SUB10C0_LWP, MEM_SUB10C0_LDP
} MEM_SUB10C0;

/* Enum declaration for MEM subcode group 1enums.  */
typedef enum mem_sub10c1 {
  MEM_SUB10C1_SB, MEM_SUB10C1_SH, MEM_SUB10C1_SW, MEM_SUB10C1_SD
 , MEM_SUB10C1_SBP, MEM_SUB10C1_SHP, MEM_SUB10C1_SWP, MEM_SUB10C1_SDP
} MEM_SUB10C1;

/* Enum declaration for MEM subcode group 2enums.  */
typedef enum mem_sub10c2 {
  MEM_SUB10C2_LBS, MEM_SUB10C2_LHS, MEM_SUB10C2_LWS, MEM_SUB10C2_DPREF
 , MEM_SUB10C2_LBSP, MEM_SUB10C2_LHSP, MEM_SUB10C2_LWSP, MEM_SUB10C2_7
} MEM_SUB10C2;

/* Enum declaration for MEM subcode group 3enums.  */
typedef enum mem_sub10c3 {
  MEM_SUB10C3_LLW, MEM_SUB10C3_SCW, MEM_SUB10C3_2, MEM_SUB10C3_3
 , MEM_SUB10C3_4, MEM_SUB10C3_5, MEM_SUB10C3_6, MEM_SUB10C3_7
} MEM_SUB10C3;

/* Enum declaration for MEM subcode group 4enums.  */
typedef enum mem_sub10c4 {
  MEM_SUB10C4_LBUP, MEM_SUB10C4_1, MEM_SUB10C4_LWUP, MEM_SUB10C4_3
 , MEM_SUB10C4_4, MEM_SUB10C4_5, MEM_SUB10C4_6, MEM_SUB10C4_7
} MEM_SUB10C4;

/* Enum declaration for MEM subcode group 5enums.  */
typedef enum mem_sub10c5 {
  MEM_SUB10C5_SBUP, MEM_SUB10C5_1, MEM_SUB10C5_SWUP, MEM_SUB10C5_3
 , MEM_SUB10C5_4, MEM_SUB10C5_5, MEM_SUB10C5_6, MEM_SUB10C5_7
} MEM_SUB10C5;

/* Enum declaration for JR subcode group 0enums.  */
typedef enum jr_sub10c0 {
  JR_SUB10C0_JR = 0, JR_SUB10C0_JRAL = 1, JR_SUB10C0_JRNEZ = 2, JR_SUB10C0_JRALNEZ = 3
 , JR_SUB10C0_4 = 4, JR_SUB10C0_5 = 5, JR_SUB10C0_6 = 6, JR_SUB10C0_7 = 7
 , JR_SUB10C0_RET = 0
} JR_SUB10C0;

/* Enum declaration for RET subcode group 0enums.  */
typedef enum ret_sub10c0 {
  RET_SUB10C0_IFRET, RET_SUB10C0_1, RET_SUB10C0_2, RET_SUB10C0_3
 , RET_SUB10C0_4, RET_SUB10C0_5, RET_SUB10C0_6, RET_SUB10C0_7
} RET_SUB10C0;

/* Enum declaration for ALU_2V2 subcode group 0enums.  */
typedef enum alu_2v2_sub10c0 {
  ALU_2V2_SUB10C0_0, ALU_2V2_SUB10C0_1, ALU_2V2_SUB10C0_2, ALU_2V2_SUB10C0_3
 , ALU_2V2_SUB10C0_4, ALU_2V2_SUB10C0_5, ALU_2V2_SUB10C0_6, ALU_2V2_SUB10C0_7
} ALU_2V2_SUB10C0;

/* Enum declaration for ALU_2V2 subcode group 1enums.  */
typedef enum alu_2v2_sub10c1 {
  ALU_2V2_SUB10C1_0, ALU_2V2_SUB10C1_1, ALU_2V2_SUB10C1_2, ALU_2V2_SUB10C1_3
 , ALU_2V2_SUB10C1_4, ALU_2V2_SUB10C1_5, ALU_2V2_SUB10C1_6, ALU_2V2_SUB10C1_7
} ALU_2V2_SUB10C1;

/* Enum declaration for ALU_2V2 subcode group 2enums.  */
typedef enum alu_2v2_sub10c2 {
  ALU_2V2_SUB10C2_0, ALU_2V2_SUB10C2_1, ALU_2V2_SUB10C2_2, ALU_2V2_SUB10C2_3
 , ALU_2V2_SUB10C2_4, ALU_2V2_SUB10C2_5, ALU_2V2_SUB10C2_6, ALU_2V2_SUB10C2_7
} ALU_2V2_SUB10C2;

/* Enum declaration for ALU_2V2 subcode group 3enums.  */
typedef enum alu_2v2_sub10c3 {
  ALU_2V2_SUB10C3_KADDH, ALU_2V2_SUB10C3_KSUBH, ALU_2V2_SUB10C3_2, ALU_2V2_SUB10C3_3
 , ALU_2V2_SUB10C3_KDMXY, ALU_2V2_SUB10C3_5, ALU_2V2_SUB10C3_6, ALU_2V2_SUB10C3_7
} ALU_2V2_SUB10C3;

/* Enum declaration for ALU_2V2 subcode group 4enums.  */
typedef enum alu_2v2_sub10c4 {
  ALU_2V2_SUB10C4_RDOV, ALU_2V2_SUB10C4_CLROV, ALU_2V2_SUB10C4_2, ALU_2V2_SUB10C4_3
 , ALU_2V2_SUB10C4_4, ALU_2V2_SUB10C4_5, ALU_2V2_SUB10C4_6, ALU_2V2_SUB10C4_7
} ALU_2V2_SUB10C4;

/* Enum declaration for ALU_2V2 subcode group 5enums.  */
typedef enum alu_2v2_sub10c5 {
  ALU_2V2_SUB10C5_MULTS64, ALU_2V2_SUB10C5_MULT64, ALU_2V2_SUB10C5_2, ALU_2V2_SUB10C5_3
 , ALU_2V2_SUB10C5_4, ALU_2V2_SUB10C5_5, ALU_2V2_SUB10C5_6, ALU_2V2_SUB10C5_7
} ALU_2V2_SUB10C5;

/* Enum declaration for ALU_2V2 subcode group 6enums.  */
typedef enum alu_2v2_sub10c6 {
  ALU_2V2_SUB10C6_0, ALU_2V2_SUB10C6_1, ALU_2V2_SUB10C6_2, ALU_2V2_SUB10C6_MADDR32
 , ALU_2V2_SUB10C6_4, ALU_2V2_SUB10C6_MSUBR32, ALU_2V2_SUB10C6_6, ALU_2V2_SUB10C6_7
} ALU_2V2_SUB10C6;

/* Enum declaration for ALU_2V2 subcode group 7enums.  */
typedef enum alu_2v2_sub10c7 {
  ALU_2V2_SUB10C7_0, ALU_2V2_SUB10C7_1, ALU_2V2_SUB10C7_2, ALU_2V2_SUB10C7_3
 , ALU_2V2_SUB10C7_4, ALU_2V2_SUB10C7_5, ALU_2V2_SUB10C7_6, ALU_2V2_SUB10C7_7
} ALU_2V2_SUB10C7;

/* Enum declaration for 5-bit extended code enums for mtsr.  */
typedef enum misc_ext5 {
  MISC_EXT5_0
} MISC_EXT5;

/* Enum declaration for 5-bit extended code enums for mtsr.  */
typedef enum mtsr_ext5 {
  MTSR_EXT5_BASE, MTSR_EXT5_SETEND, MTSR_EXT5_SETGIE
} MTSR_EXT5;

/* Enum declaration for enums for endianness value of SETEND.  */
typedef enum setend_be {
  SETEND_L, SETEND_B
} SETEND_BE;

/* Enum declaration for enums for enable bit value of SETGIE.  */
typedef enum setgie_en {
  SETGIE_D, SETGIE_E
} SETGIE_EN;

/* Enum declaration for encoding for DT/IT bits in jr insn.  */
typedef enum insn32_tr_ctl {
  TR_CTL_NT, TR_CTL_IT, TR_CTL_DT, TR_CTL_DTIT
} INSN32_TR_CTL;

/* Enum declaration for 3-bit reserved field enums.  */
typedef enum insn32_res3_7 {
  RES3_7_0
} INSN32_RES3_7;

/* Enum declaration for 1-bit reserved field enums.  */
typedef enum insn32_res1_11 {
  RES1_11_0
} INSN32_RES1_11;

/* Enum declaration for 5-bit subcode enums for MISC instructions.  */
typedef enum misc_sub5 {
  MISC_SUB5_STANDBY, MISC_SUB5_CCTL, MISC_SUB5_MFSR, MISC_SUB5_MTSR
 , MISC_SUB5_IRET, MISC_SUB5_TRAP, MISC_SUB5_TEQZ, MISC_SUB5_TNEZ
 , MISC_SUB5_DSB, MISC_SUB5_ISB, MISC_SUB5_BREAK, MISC_SUB5_SYSCALL
 , MISC_SUB5_MSYNC, MISC_SUB5_ISYNC, MISC_SUB5_TLBOP, MISC_SUB5_15
 , MISC_SUB5_16, MISC_SUB5_17, MISC_SUB5_18, MISC_SUB5_19
 , MISC_SUB5_20, MISC_SUB5_FZB
} MISC_SUB5;

/* Enum declaration for insn type 5 4-bit subcode enums.  */
typedef enum lsmw_sub4 {
  LSMW_SUB4_LMWBI, LSMW_SUB4_LMWBIM, LSMW_SUB4_LMWBD, LSMW_SUB4_LMWBDM
 , LSMW_SUB4_LMWAI, LSMW_SUB4_LMWAIM, LSMW_SUB4_LMWAD, LSMW_SUB4_LMWADM
 , LSMW_SUB4_SMWBI, LSMW_SUB4_SMWBIM, LSMW_SUB4_SMWBD, LSMW_SUB4_SMWBDM
 , LSMW_SUB4_SMWAI, LSMW_SUB4_SMWAIM, LSMW_SUB4_SMWAD, LSMW_SUB4_SMWADM
} LSMW_SUB4;

/* Enum declaration for 4-bit enable enums.  */
typedef enum lsmw_enable4 {
  LSMW_ENABLE4_0
} LSMW_ENABLE4;

/* Enum declaration for Entry point for external VIC mode.  */
typedef enum e_int_vec2 {
  E_INT_VEC_VEP0 = 9, E_INT_VEC_VEP1 = 10, E_INT_VEC_VEP2 = 11, E_INT_VEC_VEP3 = 12
 , E_INT_VEC_VEP4 = 13, E_INT_VEC_VEP5 = 14, E_INT_VEC_VEP6 = 15, E_INT_VEC_VEP7 = 16
 , E_INT_VEC_VEP8 = 17, E_INT_VEC_VEP9 = 18, E_INT_VEC_VEP10 = 19, E_INT_VEC_VEP11 = 20
 , E_INT_VEC_VEP12 = 21, E_INT_VEC_VEP13 = 22, E_INT_VEC_VEP14 = 23, E_INT_VEC_VEP15 = 24
 , E_INT_VEC_VEP16 = 25, E_INT_VEC_VEP17 = 26, E_INT_VEC_VEP18 = 27, E_INT_VEC_VEP19 = 28
 , E_INT_VEC_VEP20 = 29, E_INT_VEC_VEP21 = 30, E_INT_VEC_VEP22 = 31, E_INT_VEC_VEP23 = 32
 , E_INT_VEC_VEP24 = 33, E_INT_VEC_VEP25 = 34, E_INT_VEC_VEP26 = 35, E_INT_VEC_VEP27 = 36
 , E_INT_VEC_VEP28 = 37, E_INT_VEC_VEP29 = 38, E_INT_VEC_VEP30 = 39, E_INT_VEC_VEP31 = 40
 , E_INT_VEC_VEP32 = 41, E_INT_VEC_VEP33 = 42, E_INT_VEC_VEP34 = 43, E_INT_VEC_VEP35 = 44
 , E_INT_VEC_VEP36 = 45, E_INT_VEC_VEP37 = 46, E_INT_VEC_VEP38 = 47, E_INT_VEC_VEP39 = 48
 , E_INT_VEC_VEP40 = 49, E_INT_VEC_VEP41 = 50, E_INT_VEC_VEP42 = 51, E_INT_VEC_VEP43 = 52
 , E_INT_VEC_VEP44 = 53, E_INT_VEC_VEP45 = 54, E_INT_VEC_VEP46 = 55, E_INT_VEC_VEP47 = 56
 , E_INT_VEC_VEP48 = 57, E_INT_VEC_VEP49 = 58, E_INT_VEC_VEP50 = 59, E_INT_VEC_VEP51 = 60
 , E_INT_VEC_VEP52 = 61, E_INT_VEC_VEP53 = 62, E_INT_VEC_VEP54 = 63, E_INT_VEC_VEP55 = 64
 , E_INT_VEC_VEP56 = 65, E_INT_VEC_VEP57 = 66, E_INT_VEC_VEP58 = 67, E_INT_VEC_VEP59 = 68
 , E_INT_VEC_VEP60 = 69, E_INT_VEC_VEP61 = 70, E_INT_VEC_VEP62 = 71, E_INT_VEC_VEP63 = 72
} E_INT_VEC2;

/* Enum declaration for .  */
typedef enum gr_names {
  H_GR_P0 = 26, H_GR_P1 = 27, H_GR_FP = 28, H_GR_GP = 29
 , H_GR_LP = 30, H_GR_SP = 31, H_GR_R0 = 0, H_GR_R1 = 1
 , H_GR_R2 = 2, H_GR_R3 = 3, H_GR_R4 = 4, H_GR_R5 = 5
 , H_GR_R6 = 6, H_GR_R7 = 7, H_GR_R8 = 8, H_GR_R9 = 9
 , H_GR_R10 = 10, H_GR_R11 = 11, H_GR_R12 = 12, H_GR_R13 = 13
 , H_GR_R14 = 14, H_GR_R15 = 15, H_GR_R16 = 16, H_GR_R17 = 17
 , H_GR_R18 = 18, H_GR_R19 = 19, H_GR_R20 = 20, H_GR_R21 = 21
 , H_GR_R22 = 22, H_GR_R23 = 23, H_GR_R24 = 24, H_GR_R25 = 25
 , H_GR_R26 = 26, H_GR_R27 = 27, H_GR_R28 = 28, H_GR_R29 = 29
 , H_GR_R30 = 30, H_GR_R31 = 31, H_GR_A0 = 0, H_GR_A1 = 1
 , H_GR_A2 = 2, H_GR_A3 = 3, H_GR_A4 = 4, H_GR_A5 = 5
 , H_GR_S0 = 6, H_GR_S1 = 7, H_GR_S2 = 8, H_GR_S3 = 9
 , H_GR_S4 = 10, H_GR_S5 = 11, H_GR_S6 = 12, H_GR_S7 = 13
 , H_GR_S8 = 14, H_GR_TA = 15, H_GR_T0 = 16, H_GR_T1 = 17
 , H_GR_T2 = 18, H_GR_T3 = 19, H_GR_T4 = 20, H_GR_T5 = 21
 , H_GR_T6 = 22, H_GR_T7 = 23, H_GR_T8 = 24, H_GR_T9 = 25
 , H_GR_S9 = 28
} GR_NAMES;

/* Enum declaration for .  */
typedef enum sr_names {
  H_SR_CPU_VER = 0, H_SR_ICM_CFG = 8, H_SR_DCM_CFG = 16, H_SR_MMU_CFG = 24
 , H_SR_CR0 = 0, H_SR_CR1 = 8, H_SR_CR2 = 16, H_SR_CR3 = 24
 , H_SR_MSC_CFG = 32, H_SR_CORE_ID = 1, H_SR_FUCOP_EXIST = 40, H_SR_CR4 = 32
 , H_SR_CR5 = 1, H_SR_CR6 = 40, H_SR_PSW = 128, H_SR_IPSW = 129
 , H_SR_P_IPSW = 130, H_SR_IVB = 137, H_SR_IR0 = 128, H_SR_IR1 = 129
 , H_SR_IR2 = 130, H_SR_IR3 = 137, H_SR_EVA = 145, H_SR_P_EVA = 146
 , H_SR_ITYPE = 153, H_SR_P_ITYPE = 154, H_SR_IR4 = 145, H_SR_IR5 = 146
 , H_SR_IR6 = 153, H_SR_IR7 = 154, H_SR_MERR = 161, H_SR_IPC = 169
 , H_SR_P_IPC = 170, H_SR_OIPC = 171, H_SR_DIPC = 171, H_SR_IR8 = 161
 , H_SR_IR9 = 169, H_SR_IR10 = 170, H_SR_IR11 = 171, H_SR_P_P0 = 178
 , H_SR_P_P1 = 186, H_SR_INT_MASK = 192, H_SR_INT_PEND = 200, H_SR_IR12 = 178
 , H_SR_IR13 = 186, H_SR_IR14 = 192, H_SR_IR15 = 200, H_SR_SP_USR = 208
 , H_SR_SP_PRI = 209, H_SR_SP_PRIV = 209, H_SR_INT_PRI = 216, H_SR_INT_CTRL = 138
 , H_SR_IR16 = 208, H_SR_IR17 = 209, H_SR_IR18 = 216, H_SR_IR19 = 138
 , H_SR_SP_USR1 = 210, H_SR_SP_PRIV1 = 211, H_SR_SP_USR2 = 212, H_SR_SP_PRIV2 = 213
 , H_SR_IR20 = 210, H_SR_IR21 = 211, H_SR_IR22 = 212, H_SR_IR23 = 213
 , H_SR_SP_USR3 = 214, H_SR_SP_PRIV3 = 215, H_SR_INT_MASK2 = 193, H_SR_INT_PEND2 = 201
 , H_SR_IR24 = 214, H_SR_IR25 = 215, H_SR_IR26 = 193, H_SR_IR27 = 201
 , H_SR_INT_PRI2 = 217, H_SR_INT_TRIGGER = 204, H_SR_IR28 = 217, H_SR_IR29 = 204
 , H_SR_IR30 = 139, H_SR_MMU_CTL = 256, H_SR_L1_PPTB = 264, H_SR_TLB_VPN = 272
 , H_SR_TLB_DATA = 280, H_SR_MR0 = 256, H_SR_MR1 = 264, H_SR_MR2 = 272
 , H_SR_MR3 = 280, H_SR_TLB_MISC = 288, H_SR_VLPT_IDX = 296, H_SR_ILMB = 304
 , H_SR_DLMB = 312, H_SR_MR4 = 288, H_SR_MR5 = 296, H_SR_MR6 = 304
 , H_SR_MR7 = 312, H_SR_CACHE_CTL = 320, H_SR_HSMP_SADDR = 328, H_SR_HSMP_EADDR = 329
 , H_SR_BG_REGION = 257, H_SR_MR8 = 320, H_SR_MR9 = 328, H_SR_MR10 = 329
 , H_SR_MR11 = 257, H_SR_SDZ_CTL = 376, H_SR_MISC_CTL = 377, H_SR_N12MISC_CTL = 377
 , H_SR_IDR0 = 376, H_SR_IDR1 = 377, H_SR_BPC0 = 384, H_SR_BPA0 = 392
 , H_SR_BPAM0 = 400, H_SR_BPV0 = 408, H_SR_BPCID0 = 416, H_SR_DR0 = 384
 , H_SR_DR1 = 392, H_SR_DR2 = 400, H_SR_DR3 = 408, H_SR_DR4 = 416
 , H_SR_BPC1 = 385, H_SR_BPA1 = 393, H_SR_BPAM1 = 401, H_SR_BPV1 = 409
 , H_SR_BPCID1 = 417, H_SR_DR5 = 385, H_SR_DR6 = 393, H_SR_DR7 = 401
 , H_SR_DR8 = 409, H_SR_DR9 = 417, H_SR_BPC2 = 386, H_SR_BPA2 = 394
 , H_SR_BPAM2 = 402, H_SR_BPV2 = 410, H_SR_BPCID2 = 418, H_SR_DR10 = 386
 , H_SR_DR11 = 394, H_SR_DR12 = 402, H_SR_DR13 = 410, H_SR_DR14 = 418
 , H_SR_BPC3 = 387, H_SR_BPA3 = 395, H_SR_BPAM3 = 403, H_SR_BPV3 = 411
 , H_SR_BPCID3 = 419, H_SR_DR15 = 387, H_SR_DR16 = 395, H_SR_DR17 = 403
 , H_SR_DR18 = 411, H_SR_DR19 = 419, H_SR_BPC4 = 388, H_SR_BPA4 = 396
 , H_SR_BPAM4 = 404, H_SR_BPV4 = 412, H_SR_BPCID4 = 420, H_SR_DR20 = 388
 , H_SR_DR21 = 396, H_SR_DR22 = 404, H_SR_DR23 = 412, H_SR_DR24 = 420
 , H_SR_BPC5 = 389, H_SR_BPA5 = 397, H_SR_BPAM5 = 405, H_SR_BPV5 = 413
 , H_SR_BPCID5 = 421, H_SR_DR25 = 389, H_SR_DR26 = 397, H_SR_DR27 = 405
 , H_SR_DR28 = 413, H_SR_DR29 = 421, H_SR_BPC6 = 390, H_SR_BPA6 = 398
 , H_SR_BPAM6 = 406, H_SR_BPV6 = 414, H_SR_BPCID6 = 422, H_SR_DR30 = 390
 , H_SR_DR31 = 398, H_SR_DR32 = 406, H_SR_DR33 = 414, H_SR_DR34 = 422
 , H_SR_BPC7 = 391, H_SR_BPA7 = 399, H_SR_BPAM7 = 407, H_SR_BPV7 = 415
 , H_SR_BPCID7 = 423, H_SR_DR35 = 391, H_SR_DR36 = 399, H_SR_DR37 = 407
 , H_SR_DR38 = 415, H_SR_DR39 = 423, H_SR_EDM_CFG = 424, H_SR_EDMSW = 432
 , H_SR_EDM_CTL = 440, H_SR_EDM_DTR = 448, H_SR_DR40 = 424, H_SR_DR41 = 432
 , H_SR_DR42 = 440, H_SR_DR43 = 448, H_SR_BPMTC = 456, H_SR_DIMBR = 464
 , H_SR_TECR0 = 496, H_SR_TECR1 = 497, H_SR_DR44 = 456, H_SR_DR45 = 464
 , H_SR_DR46 = 496, H_SR_DR47 = 497, H_SR_PFMC0 = 512, H_SR_PFMC1 = 513
 , H_SR_PFMC2 = 514, H_SR_PFM_CTL = 520, H_SR_PFR0 = 512, H_SR_PFR1 = 513
 , H_SR_PFR2 = 514, H_SR_PFR3 = 520, H_SR_FUCOP_CTL = 552, H_SR_FUCPR = 552
 , H_SR_PRUSR_ACC_CTL = 544, H_SR_DMA_CFG = 640, H_SR_DMA_GCSW = 648, H_SR_DMA_CHNSEL = 656
 , H_SR_DMA_ACT = 664, H_SR_DMAR0 = 640, H_SR_DMAR1 = 648, H_SR_DMAR2 = 656
 , H_SR_DMAR3 = 664, H_SR_DMA_SETUP = 672, H_SR_DMA_ISADDR = 680, H_SR_DMA_ESADDR = 688
 , H_SR_DMA_TCNT = 696, H_SR_DMAR4 = 672, H_SR_DMAR5 = 680, H_SR_DMAR6 = 688
 , H_SR_DMAR7 = 696, H_SR_DMA_STATUS = 704, H_SR_DMA_2DSET = 712, H_SR_DMA_2DSCTL = 713
 , H_SR_DMAR8 = 704, H_SR_DMAR9 = 712, H_SR_DMAR10 = 713, H_SR_SFCR = 768
 , H_SR_SECUR0 = 768, H_SR_END = 1024
} SR_NAMES;

/* Enum declaration for .  */
typedef enum accum_hl_names {
  H_ACCUM_HL_D0_LO, H_ACCUM_HL_D0_HI, H_ACCUM_HL_D1_LO, H_ACCUM_HL_D1_HI
} ACCUM_HL_NAMES;

/* Enum declaration for .  */
typedef enum accum_names {
  H_ACCM_D0, H_ACCM_D1
} ACCUM_NAMES;

/* Enum declaration for 5-bit extended code enums for simd.  */
typedef enum simd_ext5 {
  SIMD_EXT5_0
} SIMD_EXT5;

/* Enum declaration for 5-bit subcode enums for SIMD instructions.  */
typedef enum simd_sub5 {
  SIMD_SUB5_PBSAD, SIMD_SUB5_PBSADA
} SIMD_SUB5;

/* Enum declaration for s.  */
typedef enum format16_opc_4g {
  F16_OPC_4G0, F16_OPC_4G1, F16_OPC_4G2, F16_OPC_4G3
 , F16_OPC_4G4, F16_OPC_4G5, F16_OPC_4G6, F16_OPC_4G7
 , F16_OPC_BEQZ38, F16_OPC_BNEZ38, F16_OPC_4G10, F16_OPC_4G11
 , F16_OPC_4G12, F16_OPC_4G13, F16_OPC_4G14, F16_OPC_4G15
} FORMAT16_OPC_4G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g0_1g {
  F16_OPC_4G0_MOV55, F16_OPC_4G0_MOVI55
} FORMAT16_OPC_4G0_1G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g1_2g {
  F16_OPC_4G1_ADD45, F16_OPC_4G1_SUB45, F16_OPC_4G1_ADDI45, F16_OPC_4G1_SUBI45
} FORMAT16_OPC_4G1_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g2_2g {
  F16_OPC_4G2_SRAI45, F16_OPC_4G2_SRLI45, F16_OPC_4G2_SLLI333, F16_OPC_4G2_2G3
} FORMAT16_OPC_4G2_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g2_2g3_6g_3g {
  F16_OPC_4G2_2G3_6G_ZEB33, F16_OPC_4G2_2G3_6G_ZEH33, F16_OPC_4G2_2G3_6G_SEB33, F16_OPC_4G2_2G3_6G_SEH33
 , F16_OPC_4G2_2G3_6G_XLSB33, F16_OPC_4G2_2G3_6G_X11B33, F16_OPC_4G2_2G3_6G_BMSKI33, F16_OPC_4G2_2G3_6G_FEXTI33
} FORMAT16_OPC_4G2_2G3_6G_3G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g3_2g {
  F16_OPC_4G3_ADD333, F16_OPC_4G3_SUB333, F16_OPC_4G3_ADDI333, F16_OPC_4G3_SUBI333
} FORMAT16_OPC_4G3_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g4_2g {
  F16_OPC_4G4_LWI333, F16_OPC_4G4_LWI333_BI, F16_OPC_4G4_LHI333, F16_OPC_4G4_LBI333
} FORMAT16_OPC_4G4_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g5_2g {
  F16_OPC_4G5_SWI333, F16_OPC_4G5_SWI333_BI, F16_OPC_4G5_SHI333, F16_OPC_4G5_SBI333
} FORMAT16_OPC_4G5_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g6_2g {
  F16_OPC_4G6_ADDRI36_SP, F16_OPC_4G6_LWI45_FE, F16_OPC_4G6_LWI450, F16_OPC_4G6_SWI450
} FORMAT16_OPC_4G6_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g7_3g_1g {
  F16_OPC_4G7_3G_LWI37, F16_OPC_4G7_3G_SWI37
} FORMAT16_OPC_4G7_3G_1G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g10_3g {
  F16_OPC_4G10_3_0, F16_OPC_4G10_3_1, F16_OPC_4G10_3_2, F16_OPC_4G10_3_3
 , F16_OPC_4G10_3_4, F16_OPC_4G10_J8, F16_OPC_4G10_3_6, F16_OPC_4G10_3_7
} FORMAT16_OPC_4G10_3G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g11_3g {
  F16_OPC_4G11_3_0, F16_OPC_4G11_3_1, F16_OPC_4G11_3_2, F16_OPC_4G11_3_3
 , F16_OPC_4G11_3_4, F16_OPC_4G11_3G5, F16_OPC_4G11_3_6, F16_OPC_4G11_3_7
} FORMAT16_OPC_4G11_3G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g11_3g5_3g {
  F16_OPC_4G11_3G5_JR5, F16_OPC_4G11_3G5_JRAL5, F16_OPC_4G11_3G5_EX5_IT, F16_OPC_4G11_3G5_3R3
 , F16_OPC_4G11_3G5_RET5, F16_OPC_4G11_3G5_ADD5_PC, F16_OPC_4G11_3G5_3R6, F16_OPC_4G11_3G5_3R7
} FORMAT16_OPC_4G11_3G5_3G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g12_2g {
  F16_OPC_4G12_SLTS45, F16_OPC_4G12_SLT45, F16_OPC_4G12_SLTSI45, F16_OPC_4G12_SLTI45
} FORMAT16_OPC_4G12_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g13_1g {
  F16_OPC_4G13_1G0, F16_OPC_4G13_ADDI10S
} FORMAT16_OPC_4G13_1G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g13_2g {
  F16_OPC_4G13_2G0, F16_OPC_4G13_2G1, F16_OPC_4G13_2_2, F16_OPC_4G13_2_3
} FORMAT16_OPC_4G13_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g13_3g {
  F16_OPC_4G13_BEQZS8, F16_OPC_4G13_BNEZS8, F16_OPC_4G13_3G2, F16_OPC_4G13_3_3
 , F16_OPC_4G13_3_4, F16_OPC_4G13_3_5, F16_OPC_4G13_3_6, F16_OPC_4G13_3_7
} FORMAT16_OPC_4G13_3G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g13_3g2_3g {
  F16_OPC_4G13_3G2_BREAK16, F16_OPC_4G13_3G2_3_1, F16_OPC_4G13_3G2_3_2, F16_OPC_4G13_3G2_3_3
 , F16_OPC_4G13_3G2_3_4, F16_OPC_4G13_3G2_3_5, F16_OPC_4G13_3G2_3_6, F16_OPC_4G13_3G2_3_7
} FORMAT16_OPC_4G13_3G2_3G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g14_3g_1g {
  F16_OPC_4G14_3G_LWI37_SP, F16_OPC_4G14_3G_SWI37_SP
} FORMAT16_OPC_4G14_3G_1G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g15_2g {
  F16_OPC_4G15_IFCALL9, F16_OPC_4G15_MOVPI45, F16_OPC_4G15_2G2, F16_OPC_4G15_2G3
} FORMAT16_OPC_4G15_2G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g15_3g {
  F16_OPC_4G15_3_0, F16_OPC_4G15_3_1, F16_OPC_4G15_3_2, F16_OPC_4G15_3_3
 , F16_OPC_4G15_3G4, F16_OPC_4G15_MOVD44, F16_OPC_4G15_3_6, F16_OPC_4G15_3_7
} FORMAT16_OPC_4G15_3G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g15_3g4_1g {
  F16_OPC_4G15_3G4_PUSH25, F16_OPC_4G15_3G4_POP25
} FORMAT16_OPC_4G15_3G4_1G;

/* Enum declaration for s.  */
typedef enum format16_opc_4g15_2g3_6g_3g {
  F16_OPC_4G15_2G3_6G_3R0, F16_OPC_4G15_2G3_6G_3R1, F16_OPC_4G15_2G3_6G_NEG33, F16_OPC_4G15_2G3_6G_NOT33
 , F16_OPC_4G15_2G3_6G_MUL33, F16_OPC_4G15_2G3_6G_XOR33, F16_OPC_4G15_2G3_6G_AND33, F16_OPC_4G15_2G3_6G_OR33
} FORMAT16_OPC_4G15_2G3_6G_3G;

/* Enum declaration for .  */
typedef enum gr_names_16 {
  H_GR16_R0 = 0, H_GR16_R1 = 1, H_GR16_R2 = 2, H_GR16_R3 = 3
 , H_GR16_R4 = 4, H_GR16_R5 = 5, H_GR16_R6 = 6, H_GR16_R7 = 7
 , H_GR16_R8 = 8, H_GR16_R9 = 9, H_GR16_R10 = 10, H_GR16_R11 = 11
 , H_GR16_R16 = 12, H_GR16_R17 = 13, H_GR16_R18 = 14, H_GR16_R19 = 15
 , H_GR16_H0 = 0, H_GR16_H1 = 1, H_GR16_H2 = 2, H_GR16_H3 = 3
 , H_GR16_H4 = 4, H_GR16_H5 = 5, H_GR16_H6 = 6, H_GR16_H7 = 7
 , H_GR16_H8 = 8, H_GR16_H9 = 9, H_GR16_H10 = 10, H_GR16_H11 = 11
 , H_GR16_H12 = 12, H_GR16_H13 = 13, H_GR16_H14 = 14, H_GR16_H15 = 15
 , H_GR16_A0 = 0, H_GR16_A1 = 1, H_GR16_A2 = 2, H_GR16_A3 = 3
 , H_GR16_A4 = 4, H_GR16_A5 = 5
} GR_NAMES_16;

/* Enum declaration for .  */
typedef enum gr_names_8 {
  H_GR8_R0 = 0, H_GR8_R1 = 1, H_GR8_R2 = 2, H_GR8_R3 = 3
 , H_GR8_R4 = 4, H_GR8_R5 = 5, H_GR8_R6 = 6, H_GR8_R7 = 7
 , H_GR8_O0 = 0, H_GR8_O1 = 1, H_GR8_O2 = 2, H_GR8_O3 = 3
 , H_GR8_O4 = 4, H_GR8_O5 = 5, H_GR8_O6 = 6, H_GR8_O7 = 7
 , H_GR8_A0 = 0, H_GR8_A1 = 1, H_GR8_A2 = 2, H_GR8_A3 = 3
 , H_GR8_A4 = 4, H_GR8_A5 = 5
} GR_NAMES_8;

/* Enum declaration for .  */
typedef enum gr_names_8e5 {
  H_GR8E5_R0 = 0, H_GR8E5_R1 = 1, H_GR8E5_R2 = 2, H_GR8E5_R3 = 3
 , H_GR8E5_R4 = 4, H_GR8E5_R6 = 6, H_GR8E5_R7 = 7, H_GR8E5_O0 = 0
 , H_GR8E5_O1 = 1, H_GR8E5_O2 = 2, H_GR8E5_O3 = 3, H_GR8E5_O4 = 4
 , H_GR8E5_O6 = 6, H_GR8E5_O7 = 7, H_GR8E5_A0 = 0, H_GR8E5_A1 = 1
 , H_GR8E5_A2 = 2, H_GR8E5_A3 = 3, H_GR8E5_A4 = 4
} GR_NAMES_8E5;

/* Enum declaration for .  */
typedef enum even_gr_names_16 {
  H_EVEN_GR_R0 = 0, H_EVEN_GR_A0 = 0, H_EVEN_GR_H0 = 0, H_EVEN_GR_O0 = 0
 , H_EVEN_GR_R2 = 1, H_EVEN_GR_A2 = 1, H_EVEN_GR_H2 = 1, H_EVEN_GR_O2 = 1
 , H_EVEN_GR_R4 = 2, H_EVEN_GR_A4 = 2, H_EVEN_GR_H4 = 2, H_EVEN_GR_O4 = 2
 , H_EVEN_GR_R6 = 3, H_EVEN_GR_S0 = 3, H_EVEN_GR_H6 = 3, H_EVEN_GR_O6 = 3
 , H_EVEN_GR_R8 = 4, H_EVEN_GR_S2 = 4, H_EVEN_GR_H8 = 4, H_EVEN_GR_R10 = 5
 , H_EVEN_GR_S4 = 5, H_EVEN_GR_H10 = 5, H_EVEN_GR_R12 = 6, H_EVEN_GR_S6 = 6
 , H_EVEN_GR_R14 = 7, H_EVEN_GR_S8 = 7, H_EVEN_GR_R16 = 8, H_EVEN_GR_T0 = 8
 , H_EVEN_GR_H12 = 8, H_EVEN_GR_R18 = 9, H_EVEN_GR_T2 = 9, H_EVEN_GR_H14 = 9
 , H_EVEN_GR_R20 = 10, H_EVEN_GR_T4 = 10, H_EVEN_GR_R22 = 11, H_EVEN_GR_T6 = 11
 , H_EVEN_GR_R24 = 12, H_EVEN_GR_T8 = 12, H_EVEN_GR_R26 = 13, H_EVEN_GR_P0 = 13
 , H_EVEN_GR_R28 = 14, H_EVEN_GR_FP = 14, H_EVEN_GR_S9 = 14, H_EVEN_GR_R30 = 15
 , H_EVEN_GR_LP = 15
} EVEN_GR_NAMES_16;

/* Enum declaration for insn opcode group enums.  */
typedef enum insn32_opc6c3_7 {
  OPC6C3_7_SBI_GP, OPC6C3_7_ADDI_GP
} INSN32_OPC6C3_7;

/* Enum declaration for insn opcode group enums.  */
typedef enum insn32_opc6c3_6 {
  OPC6C3_6_LHI_GP, OPC6C3_6_LHSI_GP, OPC6C3_6_SHI_GP, OPC6C3_6_XWI_GP
} INSN32_OPC6C3_6;

/* Enum declaration for insn opcode group enums.  */
typedef enum insn32_opc6c3_6_3 {
  OPC6C3_6_3_LWI_GP, OPC6C3_6_3_SWI_GP
} INSN32_OPC6C3_6_3;

/* Enum declaration for insn opcode group enums.  */
typedef enum insn32_opc6c2_7 {
  OPC6C2_7_LBI_GP, OPC6C2_7_LBSI_GP
} INSN32_OPC6C2_7;

/* Enum declaration for 5-bit subcode domain enums.  */
typedef enum insn32_subop {
  SUB5BITS_OPC_ADD_SLLI, SUB5BITS_OPC_SUB_SLLI, SUB5BITS_OPC_AND_SLLI, SUB5BITS_OPC_XOR_SLLI
 , SUB5BITS_OPC_OR_SLLI, SUB5BITS_OPC_5, SUB5BITS_OPC_6, SUB5BITS_OPC_7
 , SUB5BITS_OPC_8, SUB5BITS_OPC_9, SUB5BITS_OPC_10, SUB5BITS_OPC_11
 , SUB5BITS_OPC_12, SUB5BITS_OPC_13, SUB5BITS_OPC_14, SUB5BITS_OPC_15
 , SUB5BITS_OPC_16, SUB5BITS_OPC_17, SUB5BITS_OPC_18, SUB5BITS_OPC_19
 , SUB5BITS_OPC_20, SUB5BITS_OPC_OR_SRLI, SUB5BITS_OPC_22, SUB5BITS_OPC_23
 , SUB5BITS_OPC_24, SUB5BITS_OPC_25, SUB5BITS_OPC_26, SUB5BITS_OPC_27
 , SUB5BITS_OPC_ADD_SRLI, SUB5BITS_OPC_SUB_SRLI, SUB5BITS_OPC_AND_SRLI, SUB5BITS_OPC_XOR_SRLI
} INSN32_SUBOP;

/* Enum declaration for BR3.  */
typedef enum insn32_3g5_br3_5g_ {
  OPC3G5_BR3_5G_BEQC, OPC3G5_BR3_5G_BNEC
} INSN32_3G5_BR3_5G_;

/* Enum declaration for bit 24-23 opcode enums.  */
typedef enum insn32_op2_24_a {
  AOP2_24_0, AOP2_24_1, AOP2_24_2, AOP2_24_3
} INSN32_OP2_24_A;

/* Enum declaration for bit 22-20 opcode enums.  */
typedef enum insn32_op3_22_a {
  AOP3_22_0, AOP3_22_1, AOP3_22_2, AOP3_22_3
 , AOP3_22_4, AOP3_22_5, AOP3_22_6, AOP3_22_7
} INSN32_OP3_22_A;

/* Enum declaration for bit 22-20 opcode enums.  */
typedef enum insn32_op3_am_a {
  AM_AMADD = 0, AM_AMSUB = 1, AM_AMULT = 2, AM_3 = 3
 , AM_AMADDS = 4, AM_AMSUBS = 5, AM_AMULTS = 6, AM_AMNEGS = 7
 , AM_AMABB = 0, AM_AMABT = 1, AM_AMATB = 2, AM_AMATT = 3
 , AM_AMBB = 4, AM_AMBT = 5, AM_AMTB = 6, AM_AMTT = 7
 , AM_AMAWB = 4, AM_AMAWT = 5, AM_AMWB = 6, AM_AMWT = 7
} INSN32_OP3_AM_A;

/* Enum declaration for bit 8-6 opcode enums.  */
typedef enum insn32_op3_8_a {
  AOP3_8_0, AOP3_8_1, AOP3_8_2, AOP3_8_3
 , AOP3_8_4, AOP3_8_5, AOP3_8_6, AOP3_8_7
} INSN32_OP3_8_A;

/* Enum declaration for bit 8-7 opcode enums.  */
typedef enum insn32_op2_8_a {
  AOP2_8_0, AOP2_8_1, AOP2_8_2, AOP2_8_3
} INSN32_OP2_8_A;

/* Enum declaration for bit 5 opcode enums.  */
typedef enum insn32_op1_5_a {
  AOP1_5_0, AOP1_5_1
} INSN32_OP1_5_A;

/* Enum declaration for bit 5- 4 reserved enums.  */
typedef enum insn32_res5_4_a {
  ARES5_4_0, ARES5_4_1, ARES5_4_2
} INSN32_RES5_4_A;

/* Enum declaration for bit 1- 9 reserved enums.  */
typedef enum insn32_res1_9_a {
  ARES1_9_0, ARES1_9_1
} INSN32_RES1_9_A;

/* Enum declaration for bit 19-17 reserved enums.  */
typedef enum insn32_res3_19_a {
  ARES3_19_0
} INSN32_RES3_19_A;

/* Enum declaration for bit 16-15 reserved enums.  */
typedef enum insn32_res2_16_a {
  ARES2_16_0
} INSN32_RES2_16_A;

/* Enum declaration for bit 14-10 reserved enums.  */
typedef enum insn32_res5_14_a {
  ARES5_14_0
} INSN32_RES5_14_A;

/* Enum declaration for bit 4-0 fake opcode enums.  */
typedef enum insn32_fake5_4_a {
  AFAKE5_4_0, AFAKE5_4_1
} INSN32_FAKE5_4_A;

/* Enum declaration for 1-bit reserved field enums.  */
typedef enum insn32_res1_25 {
  RES1_25_0
} INSN32_RES1_25;

/* Enum declaration for 1-bit sub code from bit field 25.  */
typedef enum insn32_sub1_25 {
  SUB1_25_0, SUB1_25_1
} INSN32_SUB1_25;

/* Enum declaration for 3-bits sub code from bit field 22.  */
typedef enum insn32_sub3_22 {
  SUB3_22_EQ, SUB3_22_LT, SUB3_22_LE, SUB3_22_UN
} INSN32_SUB3_22;

/* Enum declaration for 4-bits sub code enums for floating insn.  */
typedef enum fpinsn_sub4_22 {
  FP_SUB4_22_SR = 0, FP_SUB4_22_DR = 1, FP_SUB4_22_XR = 12
} FPINSN_SUB4_22;

/* Enum declaration for 5-bits sub code enums for floating insn.  */
typedef enum fpinsn_sub5_17 {
  FP_SUB5_17_CFG, FP_SUB5_17_CSR
} FPINSN_SUB5_17;

/* Enum declaration for 1-bit subcode enums for floating point insn.  */
typedef enum fpu_sub1_24 {
  FPU_SUB1_24_0, FPU_SUB1_24_1
} FPU_SUB1_24;

/* Enum declaration for 1-bit subcode enums for floating point insn.  */
typedef enum fpu_sub1_19 {
  FPU_SUB1_19_0, FPU_SUB1_19_1
} FPU_SUB1_19;

/* Enum declaration for coprocessor enums.  */
typedef enum insn32_cop0_cp_26 {
  COP_0_CP26_0, COP_0_CP26_1, COP_0_CP26_2, COP_0_CP26_3
} INSN32_COP0_CP_26;

/* Enum declaration for coprocessor enums.  */
typedef enum insn32_cop0_cp_17 {
  COP_0_CP17_0, COP_0_CP17_1, COP_0_CP17_2, COP_0_CP17_3
} INSN32_COP0_CP_17;

/* Enum declaration for cpe group enums.  */
typedef enum cop_0_cpeg {
  COP_0_CPEG_0, COP_0_CPEG_1, COP_0_CPEG_2, COP_0_CPEG_3
} COP_0_CPEG;

/* Enum declaration for cpe code enums in cpe group0.  */
typedef enum cop_0_cpeg0 {
  COP_0_CPEG0_FS1, COP_0_CPEG0_MFCP, COP_0_CPEG0_FLS, COP_0_CPEG0_FLD
} COP_0_CPEG0;

/* Enum declaration for cpe code enums in cpe group1.  */
typedef enum cop_0_cpeg1 {
  COP_0_CPEG1_FS2, COP_0_CPEG1_1, COP_0_CPEG1_2, COP_0_CPEG1_3
} COP_0_CPEG1;

/* Enum declaration for cpe code enums in cpe group2.  */
typedef enum cop_0_cpeg2 {
  COP_0_CPEG2_FD1, COP_0_CPEG2_MTCP, COP_0_CPEG2_FSS, COP_0_CPEG2_FSD
} COP_0_CPEG2;

/* Enum declaration for cpe code enums in cpe group3.  */
typedef enum cop_0_cpeg3 {
  COP_0_CPEG3_FD2, COP_0_CPEG3_1, COP_0_CPEG3_2, COP_0_CPEG3_3
} COP_0_CPEG3;

/* Enum declaration for fs1 group enums.  */
typedef enum cop_0_fs1g {
  COP_0_FS1G_0, COP_0_FS1G_1, COP_0_FS1G_2, COP_0_FS1G_3
} COP_0_FS1G;

/* Enum declaration for fs1 code enums in fs1 group0.  */
typedef enum cop_0_fs1g0 {
  COP_0_FS1G0_FADDS, COP_0_FS1G0_FSUBS, COP_0_FS1G0_FCPYNSS, COP_0_FS1G0_FCPYSS
} COP_0_FS1G0;

/* Enum declaration for fs1 code enums in fs1 group1.  */
typedef enum cop_0_fs1g1 {
  COP_0_FS1G1_FMADDS, COP_0_FS1G1_FMSUBS, COP_0_FS1G1_FCMOVNS, COP_0_FS1G1_FCMOVZS
} COP_0_FS1G1;

/* Enum declaration for fs1 code enums in fs1 group2.  */
typedef enum cop_0_fs1g2 {
  COP_0_FS1G2_FNMADDS, COP_0_FS1G2_FNMSUBS, COP_0_FS1G2_2, COP_0_FS1G2_3
} COP_0_FS1G2;

/* Enum declaration for fs1 code enums in fs1 group3.  */
typedef enum cop_0_fs1g3 {
  COP_0_FS1G3_FMULS, COP_0_FS1G3_FDIVS, COP_0_FS1G3_2, COP_0_FS1G3_F2OP
} COP_0_FS1G3;

/* Enum declaration for fs1/f2op group enums.  */
typedef enum cop_0_fs1_f2opg {
  COP_0_FS1_F2OPG_0, COP_0_FS1_F2OPG_1, COP_0_FS1_F2OPG_2, COP_0_FS1_F2OPG_3
 , COP_0_FS1_F2OPG_4, COP_0_FS1_F2OPG_5, COP_0_FS1_F2OPG_6, COP_0_FS1_F2OPG_7
} COP_0_FS1_F2OPG;

/* Enum declaration for fs1/f2op code enums in fs1/f2op group0.  */
typedef enum cop_0_fs1_f2opg0 {
  COP_0_FS1_F2OPG0_FS2D, COP_0_FS1_F2OPG0_FSQRTS
} COP_0_FS1_F2OPG0;

/* Enum declaration for fs1/f2op code enums in fs1/f2op group1.  */
typedef enum cop_0_fs1_f2opg1 {
  COP_0_FS1_F2OPG1_0, COP_0_FS1_F2OPG1_FABSS
} COP_0_FS1_F2OPG1;

/* Enum declaration for fs1/f2op code enums in fs1/f2op group2.  */
typedef enum cop_0_fs1_f2opg2 {
  COP_0_FS1_F2OPG2_FUI2S, COP_0_FS1_F2OPG2_1
} COP_0_FS1_F2OPG2;

/* Enum declaration for fs1/f2op code enums in fs1/f2op group3.  */
typedef enum cop_0_fs1_f2opg3 {
  COP_0_FS1_F2OPG3_FSI2S, COP_0_FS1_F2OPG3_1
} COP_0_FS1_F2OPG3;

/* Enum declaration for fs1/f2op code enums in fs1/f2op group4.  */
typedef enum cop_0_fs1_f2opg4 {
  COP_0_FS1_F2OPG4_FS2UI, COP_0_FS1_F2OPG4_1
} COP_0_FS1_F2OPG4;

/* Enum declaration for fs1/f2op code enums in fs1/f2op group5.  */
typedef enum cop_0_fs1_f2opg5 {
  COP_0_FS1_F2OPG5_FS2UIZ, COP_0_FS1_F2OPG5_1
} COP_0_FS1_F2OPG5;

/* Enum declaration for fs1/f2op code enums in fs1/f2op group6.  */
typedef enum cop_0_fs1_f2opg6 {
  COP_0_FS1_F2OPG6_FS2SI, COP_0_FS1_F2OPG6_1
} COP_0_FS1_F2OPG6;

/* Enum declaration for fs1/f2op code enums in fs1/f2op group7.  */
typedef enum cop_0_fs1_f2opg7 {
  COP_0_FS1_F2OPG7_FS2SIZ, COP_0_FS1_F2OPG7_1
} COP_0_FS1_F2OPG7;

/* Enum declaration for fs2 group enums.  */
typedef enum cop_0_fs2g {
  COP_0_FS2G_0, COP_0_FS2G_1, COP_0_FS2G_2, COP_0_FS2G_3
} COP_0_FS2G;

/* Enum declaration for fs2 code enums in fs2 group0.  */
typedef enum cop_0_fs2g0 {
  COP_0_FS2G0_FCMPEQS, COP_0_FS2G0_FCMPEQSE
} COP_0_FS2G0;

/* Enum declaration for fs2 code enums in fs2 group1.  */
typedef enum cop_0_fs2g1 {
  COP_0_FS2G1_FCMPLTS, COP_0_FS2G1_FCMPLTSE
} COP_0_FS2G1;

/* Enum declaration for fs2 code enums in fs2 group2.  */
typedef enum cop_0_fs2g2 {
  COP_0_FS2G2_FCMPLES, COP_0_FS2G2_FCMPLESE
} COP_0_FS2G2;

/* Enum declaration for fs2 code enums in fs2 group3.  */
typedef enum cop_0_fs2g3 {
  COP_0_FS2G3_FCMPUNS, COP_0_FS2G3_FCMPUNSE
} COP_0_FS2G3;

/* Enum declaration for fd1 group enums.  */
typedef enum cop_0_fd1g {
  COP_0_FD1G_0, COP_0_FD1G_1, COP_0_FD1G_2, COP_0_FD1G_3
} COP_0_FD1G;

/* Enum declaration for fd1 code enums in fd1 group0.  */
typedef enum cop_0_fd1g0 {
  COP_0_FD1G0_FADDD, COP_0_FD1G0_FSUBD, COP_0_FD1G0_FCPYNSD, COP_0_FD1G0_FCPYSD
} COP_0_FD1G0;

/* Enum declaration for fd1 code enums in fd1 group1.  */
typedef enum cop_0_fd1g1 {
  COP_0_FD1G1_FMADDD, COP_0_FD1G1_FMSUBD, COP_0_FD1G1_FCMOVND, COP_0_FD1G1_FCMOVZD
} COP_0_FD1G1;

/* Enum declaration for fd1 code enums in fd1 group2.  */
typedef enum cop_0_fd1g2 {
  COP_0_FD1G2_FNMADDD, COP_0_FD1G2_FNMSUBD, COP_0_FD1G2_2, COP_0_FD1G2_3
} COP_0_FD1G2;

/* Enum declaration for fd1 code enums in fd1 group3.  */
typedef enum cop_0_fd1g3 {
  COP_0_FD1G3_FMULD, COP_0_FD1G3_FDIVD, COP_0_FD1G3_2, COP_0_FD1G3_F2OP
} COP_0_FD1G3;

/* Enum declaration for fd1/f2op group enums.  */
typedef enum cop_0_fd1_f2opg {
  COP_0_FD1_F2OPG_0, COP_0_FD1_F2OPG_1, COP_0_FD1_F2OPG_2, COP_0_FD1_F2OPG_3
 , COP_0_FD1_F2OPG_4, COP_0_FD1_F2OPG_5, COP_0_FD1_F2OPG_6, COP_0_FD1_F2OPG_7
} COP_0_FD1_F2OPG;

/* Enum declaration for fd1 code enums in fd1 group0.  */
typedef enum cop_0_fd1_f2opg0 {
  COP_0_FD1_F2OPG0_FD2S, COP_0_FD1_F2OPG0_FSQRTD, COP_0_FD1_F2OPG0_2, COP_0_FD1_F2OPG0_3
} COP_0_FD1_F2OPG0;

/* Enum declaration for fd1 code enums in fd1 group1.  */
typedef enum cop_0_fd1_f2opg1 {
  COP_0_FD1_F2OPG1_0, COP_0_FD1_F2OPG1_FABSD, COP_0_FD1_F2OPG1_2, COP_0_FD1_F2OPG1_3
} COP_0_FD1_F2OPG1;

/* Enum declaration for fd1 code enums in fd1 group2.  */
typedef enum cop_0_fd1_f2opg2 {
  COP_0_FD1_F2OPG2_FUI2D, COP_0_FD1_F2OPG2_1, COP_0_FD1_F2OPG2_2, COP_0_FD1_F2OPG2_3
} COP_0_FD1_F2OPG2;

/* Enum declaration for fd1 code enums in fd1 group3.  */
typedef enum cop_0_fd1_f2opg3 {
  COP_0_FD1_F2OPG3_FSI2D, COP_0_FD1_F2OPG3_1, COP_0_FD1_F2OPG3_2, COP_0_FD1_F2OPG3_3
} COP_0_FD1_F2OPG3;

/* Enum declaration for fd1 code enums in fd1 group4.  */
typedef enum cop_0_fd1_f2opg4 {
  COP_0_FD1_F2OPG4_FD2UI, COP_0_FD1_F2OPG4_1, COP_0_FD1_F2OPG4_2, COP_0_FD1_F2OPG4_3
} COP_0_FD1_F2OPG4;

/* Enum declaration for fd1 code enums in fd1 group5.  */
typedef enum cop_0_fd1_f2opg5 {
  COP_0_FD1_F2OPG5_FD2UIZ, COP_0_FD1_F2OPG5_1, COP_0_FD1_F2OPG5_2, COP_0_FD1_F2OPG5_3
} COP_0_FD1_F2OPG5;

/* Enum declaration for fd1 code enums in fd1 group6.  */
typedef enum cop_0_fd1_f2opg6 {
  COP_0_FD1_F2OPG6_FD2SI, COP_0_FD1_F2OPG6_1, COP_0_FD1_F2OPG6_2, COP_0_FD1_F2OPG6_3
} COP_0_FD1_F2OPG6;

/* Enum declaration for fd1 code enums in fd1 group7.  */
typedef enum cop_0_fd1_f2opg7 {
  COP_0_FD1_F2OPG7_FD2SIZ, COP_0_FD1_F2OPG7_1, COP_0_FD1_F2OPG7_2, COP_0_FD1_F2OPG7_3
} COP_0_FD1_F2OPG7;

/* Enum declaration for fd2 group enums.  */
typedef enum cop_0_fd2g {
  COP_0_FD2G_0, COP_0_FD2G_1, COP_0_FD2G_2, COP_0_FD2G_3
} COP_0_FD2G;

/* Enum declaration for fd2 code enums in fd2 group0.  */
typedef enum cop_0_fd2g0 {
  COP_0_FD2G0_FCMPEQD, COP_0_FD2G0_FCMPEQDE
} COP_0_FD2G0;

/* Enum declaration for fd2 code enums in fd2 group1.  */
typedef enum cop_0_fd2g1 {
  COP_0_FD2G1_FCMPLTD, COP_0_FD2G1_FCMPLTDE
} COP_0_FD2G1;

/* Enum declaration for fd2 code enums in fd2 group2.  */
typedef enum cop_0_fd2g2 {
  COP_0_FD2G2_FCMPLED, COP_0_FD2G2_FCMPLEDE
} COP_0_FD2G2;

/* Enum declaration for fd2 code enums in fd2 group3.  */
typedef enum cop_0_fd2g3 {
  COP_0_FD2G3_FCMPUND, COP_0_FD2G3_FCMPUNDE
} COP_0_FD2G3;

/* Enum declaration for .  */
typedef enum fcsr_names {
  H_FCSR_FPCFG, H_FCSR_FPCSR
} FCSR_NAMES;

/* Enum declaration for .  */
typedef enum fsr_names {
  H_FSR_FS0, H_FSR_FS1, H_FSR_FS2, H_FSR_FS3
 , H_FSR_FS4, H_FSR_FS5, H_FSR_FS6, H_FSR_FS7
 , H_FSR_FS8, H_FSR_FS9, H_FSR_FS10, H_FSR_FS11
 , H_FSR_FS12, H_FSR_FS13, H_FSR_FS14, H_FSR_FS15
 , H_FSR_FS16, H_FSR_FS17, H_FSR_FS18, H_FSR_FS19
 , H_FSR_FS20, H_FSR_FS21, H_FSR_FS22, H_FSR_FS23
 , H_FSR_FS24, H_FSR_FS25, H_FSR_FS26, H_FSR_FS27
 , H_FSR_FS28, H_FSR_FS29, H_FSR_FS30, H_FSR_FS31
} FSR_NAMES;

/* Enum declaration for .  */
typedef enum fdr_names {
  H_FDR_FD0, H_FDR_FD1, H_FDR_FD2, H_FDR_FD3
 , H_FDR_FD4, H_FDR_FD5, H_FDR_FD6, H_FDR_FD7
 , H_FDR_FD8, H_FDR_FD9, H_FDR_FD10, H_FDR_FD11
 , H_FDR_FD12, H_FDR_FD13, H_FDR_FD14, H_FDR_FD15
} FDR_NAMES;

/* Enum declaration for .  */
typedef enum cpr_names {
  H_COP_DR_CPR0, H_COP_DR_CPR1, H_COP_DR_CPR2, H_COP_DR_CPR3
 , H_COP_DR_CPR4, H_COP_DR_CPR5, H_COP_DR_CPR6, H_COP_DR_CPR7
 , H_COP_DR_CPR8, H_COP_DR_CPR9, H_COP_DR_CPR10, H_COP_DR_CPR11
 , H_COP_DR_CPR12, H_COP_DR_CPR13, H_COP_DR_CPR14, H_COP_DR_CPR15
 , H_COP_DR_CPR16, H_COP_DR_CPR17, H_COP_DR_CPR18, H_COP_DR_CPR19
 , H_COP_DR_CPR20, H_COP_DR_CPR21, H_COP_DR_CPR22, H_COP_DR_CPR23
 , H_COP_DR_CPR24, H_COP_DR_CPR25, H_COP_DR_CPR26, H_COP_DR_CPR27
 , H_COP_DR_CPR28, H_COP_DR_CPR29, H_COP_DR_CPR30, H_COP_DR_CPR31
} CPR_NAMES;

/* Enum declaration for cpe group enums.  */
typedef enum cop_cpeg {
  COP_CPEG_0, COP_CPEG_1, COP_CPEG_2, COP_CPEG_3
} COP_CPEG;

/* Enum declaration for mfcp/mtcp group enums.  */
typedef enum mftcp {
  MFTCP_W, MFTCP_D, MFTCP_2, MFTCP_PW
} MFTCP;

/* Enum declaration for cpe code enums in cpe group0.  */
typedef enum cop_cpeg0 {
  COP_CPEG0_CPE1, COP_CPEG0_MFCP, COP_CPEG0_CPLW, COP_CPEG0_CPLD
} COP_CPEG0;

/* Enum declaration for cpe code enums in cpe group1.  */
typedef enum cop_cpeg1 {
  COP_CPEG1_CPE2, COP_CPEG1_1, COP_CPEG1_2, COP_CPEG1_3
} COP_CPEG1;

/* Enum declaration for cpe code enums in cpe group2.  */
typedef enum cop_cpeg2 {
  COP_CPEG2_CPE3, COP_CPEG2_MTCP, COP_CPEG2_CPSW, COP_CPEG2_CPSD
} COP_CPEG2;

/* Enum declaration for cpe code enums in cpe group3.  */
typedef enum cop_cpeg3 {
  COP_CPEG3_CPE4, COP_CPEG3_1, COP_CPEG3_2, COP_CPEG3_3
} COP_CPEG3;

/* Enum declaration for 1 bit enums for FFB field.  */
typedef enum insn32_op1_s {
  OP1_S_0, OP1_S_1
} INSN32_OP1_S;

/* Enum declaration for 5-bit enums for USTAT1.  */
typedef enum insn32_5_12 {
  SUB5_12_USTAT = 30
} INSN32_5_12;

/* Enum declaration for 5-bit enums for USTAT2.  */
typedef enum insn32_5_17 {
  SUB5_17_0
} INSN32_5_17;

/* Attributes.  */

/* Enum declaration for machine type selection.  */
typedef enum mach_attr {
  MACH_BASE, MACH_N1H, MACH_N1H_V2, MACH_N1H_V3
 , MACH_N1H_V3M, MACH_MAX
} MACH_ATTR;

/* Enum declaration for instruction set selection.  */
typedef enum isa_attr {
  ISA_NDS32, ISA_MAX
} ISA_ATTR;

/* Enum declaration for parallel execution pipeline selection.  */
typedef enum pipe_attr {
  PIPE_NONE, PIPE_O, PIPE_S, PIPE_OS
} PIPE_ATTR;

/* Number of architecture variants.  */
#define MAX_ISAS  1
#define MAX_MACHS ((int) MACH_MAX)

/* Ifield support.  */

/* Ifield attribute indices.  */

/* Enum declaration for cgen_ifld attrs.  */
typedef enum cgen_ifld_attr {
  CGEN_IFLD_VIRTUAL, CGEN_IFLD_PCREL_ADDR, CGEN_IFLD_ABS_ADDR, CGEN_IFLD_RESERVED
 , CGEN_IFLD_SIGN_OPT, CGEN_IFLD_SIGNED, CGEN_IFLD_RELOC, CGEN_IFLD_END_BOOLS
 , CGEN_IFLD_START_NBOOLS = 31, CGEN_IFLD_MACH, CGEN_IFLD_END_NBOOLS
} CGEN_IFLD_ATTR;

/* Number of non-boolean elements in cgen_ifld_attr.  */
#define CGEN_IFLD_NBOOL_ATTRS (CGEN_IFLD_END_NBOOLS - CGEN_IFLD_START_NBOOLS - 1)

/* cgen_ifld attribute accessor macros.  */
#define CGEN_ATTR_CGEN_IFLD_MACH_VALUE(attrs) ((attrs)->nonbool[CGEN_IFLD_MACH-CGEN_IFLD_START_NBOOLS-1].nonbitset)
#define CGEN_ATTR_CGEN_IFLD_VIRTUAL_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_IFLD_VIRTUAL)) != 0)
#define CGEN_ATTR_CGEN_IFLD_PCREL_ADDR_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_IFLD_PCREL_ADDR)) != 0)
#define CGEN_ATTR_CGEN_IFLD_ABS_ADDR_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_IFLD_ABS_ADDR)) != 0)
#define CGEN_ATTR_CGEN_IFLD_RESERVED_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_IFLD_RESERVED)) != 0)
#define CGEN_ATTR_CGEN_IFLD_SIGN_OPT_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_IFLD_SIGN_OPT)) != 0)
#define CGEN_ATTR_CGEN_IFLD_SIGNED_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_IFLD_SIGNED)) != 0)
#define CGEN_ATTR_CGEN_IFLD_RELOC_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_IFLD_RELOC)) != 0)

/* Enum declaration for nds32 ifield types.  */
typedef enum ifield_type {
  NDS32_F_NIL, NDS32_F_ANYOF, NDS32_F_IFMT, NDS32_F_32_OPC6G
 , NDS32_F_32_OPC6C, NDS32_F_32_SUB1, NDS32_F_32_RT5, NDS32_F_32_RA5
 , NDS32_F_32_RB5, NDS32_F_32_RD24, NDS32_F_32_RD1, NDS32_F_32_RD20
 , NDS32_F_32_RD1HL, NDS32_F_32_USR, NDS32_F_32_GROUP, NDS32_F_32_SR10
 , NDS32_F_32T0_DISP24, NDS32_F_32_CONCAT24, NDS32_F_32T1_SLO20, NDS32_F_32T1_UHI20
 , NDS32_F_32T1_DISP16, NDS32_F_32T1_DISP9, NDS32_F_32T1_SUB4, NDS32_F_32T2_SLO15D
 , NDS32_F_32T2_ULO15D, NDS32_F_32T2_SLO15W, NDS32_F_32T2_ULO15W, NDS32_F_32T2_SLO15H
 , NDS32_F_32T2_ULO15H, NDS32_F_32T2_SLO15B, NDS32_F_32T2_ULO15B, NDS32_F_32T2_DISP14
 , NDS32_F_32T2_SUB1, NDS32_F_32T3_RES10_7, NDS32_F_32T3_RES12_12, NDS32_F_32T3_SWID15
 , NDS32_F_32T3_SUB10, NDS32_F_32T3_SUB10SI, NDS32_F_32T3_SUB10DSI, NDS32_F_32T3_SUB10D
 , NDS32_F_32T3_SUB10G, NDS32_F_32T3_SUB10G2, NDS32_F_32T3_SUB10C, NDS32_F_32T3_UIMM5
 , NDS32_F_32T3_EXT3, NDS32_F_32T4_EXT5, NDS32_F_32T4_EXT2, NDS32_F_32T4_RES3_22
 , NDS32_F_32T4_SUB5, NDS32_F_32T5_MASK4, NDS32_F_32T5_SUB4, NDS32_F_32T5_RES2
 , NDS32_F_32T2_ST4, NDS32_F_32TX_4_17, NDS32_F_32TX_1_21, NDS32_F_32_GROUP_USR
 , NDS32_F_16_OPC1, NDS32_F_16_OPC14, NDS32_F_16_OPC141, NDS32_F_16_OPC142
 , NDS32_F_16_OPC143, NDS32_F_16_OPC1431, NDS32_F_16_OPC1433, NDS32_F_16_OPC14332
 , NDS32_F_16_OPC143323, NDS32_F_16_RT5H, NDS32_F_16_RA5H, NDS32_F_16_RB5H
 , NDS32_F_16_RT4, NDS32_F_16_RA4, NDS32_F_16_RT3, NDS32_F_16_RT3_7
 , NDS32_F_16_RA3, NDS32_F_16_RB3, NDS32_F_16_UIMM3, NDS32_F_16_ULO3W
 , NDS32_F_16_ULO3H, NDS32_F_16_ULO3B, NDS32_F_16_UIMM5, NDS32_F_16_SIMM5
 , NDS32_F_16_ULO7W, NDS32_F_16_HSDISP8, NDS32_F_16_SWID5, NDS32_F_16_SWID9
 , NDS32_F_16_SIMM10, NDS32_F_16_RT5E, NDS32_F_16_RA5E, NDS32_F_16_MASK2
 , NDS32_F_16_UIMM3_10, NDS32_F_16_UIMM5D, NDS32_F_16_UIMM6W, NDS32_F_16_SUIMM5
 , NDS32_F_16_SIMM5W, NDS32_F_32_SLO19, NDS32_F_32_SLO17W, NDS32_F_32_SLO18H
 , NDS32_F_32V2_19_1, NDS32_F_32V2_19_2, NDS32_F_32V2_17_1, NDS32_F_32_RS5
 , NDS32_F_32T1_DISP8, NDS32_F_32T21_SUB1, NDS32_F_32T2_SIMM11, NDS32_F_32T21_ULO5
 , NDS32_F_32T21_SUBOP, NDS32_F_32_OP2_24_A, NDS32_F_32_OP3_22_A, NDS32_F_32_OP3_AM_A
 , NDS32_F_32_RA5_A, NDS32_F_32_RD5_A, NDS32_F_32_RES3_19_A, NDS32_F_32_ARIDX4_A
 , NDS32_F_32_DH2_16_A, NDS32_F_32_RES2_16_A, NDS32_F_32_IMM16_A, NDS32_F_32_RB5_A
 , NDS32_F_32_RES5_14_A, NDS32_F_32_D1_A, NDS32_F_32_RES1_9_A, NDS32_F_32_OP3_8_A
 , NDS32_F_32_OP2_8_A, NDS32_F_32_DH2_6_A, NDS32_F_32_OP1_5_A, NDS32_F_32_RES1_5_A
 , NDS32_F_32_ARIDX5_A, NDS32_F_32_LSBLOC_A, NDS32_F_32_RES5_4_A, NDS32_F_32_RC4_A
 , NDS32_F_32_M2_5_A, NDS32_F_32_IM1_4_A, NDS32_F_32_M2_3_A, NDS32_F_32_I2_1_A
 , NDS32_F_32_RA4_19_A, NDS32_F_32_C1_15_A, NDS32_F_32_RB3_14_A, NDS32_F_32_RC2_11_A
 , NDS32_F_32_RC1_5_A, NDS32_F_32_RC5_0_A, NDS32_F_32_RC5_1_A, NDS32_F_32_IM5_I_A
 , NDS32_F_32_IM5_M_A, NDS32_F_32_RB5P_A, NDS32_F_32_IM6_I_0_A, NDS32_F_32_IM6_I_1_A
 , NDS32_F_32_IM6_M_0_A, NDS32_F_32_IM6_M_1_A, NDS32_F_32_R10A5_A, NDS32_F_32_R10B5_A
 , NDS32_F_32_R10C5_A, NDS32_F_32_R10C5_0_A, NDS32_F_32_R10C5_1_A, NDS32_F_32TX_2_17
 , NDS32_F_32TX_3_17, NDS32_F_32TX_5_17, NDS32_F_32TX_1_19, NDS32_F_32TX_2_20
 , NDS32_F_32TX_12_20, NDS32_F_32TX_2_22, NDS32_F_32TX_3_22, NDS32_F_32TX_4_22
 , NDS32_F_32TX_1_24, NDS32_F_32TX_2_24, NDS32_F_32TX_2_26, NDS32_F_32TX_1_25
 , NDS32_F_32TX_2_28, NDS32_F_32TX_2_30, NDS32_F_32TX_SLO12W, NDS32_F_32TX_SLO12D
 , NDS32_F_32_19_7, NDS32_F_32_12_12, NDS32_F_32_2_26, NDS32_F_32_OP1_S
 , NDS32_F_32_UIMM8_S, NDS32_F_MAX
} IFIELD_TYPE;

#define MAX_IFLD ((int) NDS32_F_MAX)

/* Hardware attribute indices.  */

/* Enum declaration for cgen_hw attrs.  */
typedef enum cgen_hw_attr {
  CGEN_HW_VIRTUAL, CGEN_HW_CACHE_ADDR, CGEN_HW_PC, CGEN_HW_PROFILE
 , CGEN_HW_END_BOOLS, CGEN_HW_START_NBOOLS = 31, CGEN_HW_MACH, CGEN_HW_END_NBOOLS
} CGEN_HW_ATTR;

/* Number of non-boolean elements in cgen_hw_attr.  */
#define CGEN_HW_NBOOL_ATTRS (CGEN_HW_END_NBOOLS - CGEN_HW_START_NBOOLS - 1)

/* cgen_hw attribute accessor macros.  */
#define CGEN_ATTR_CGEN_HW_MACH_VALUE(attrs) ((attrs)->nonbool[CGEN_HW_MACH-CGEN_HW_START_NBOOLS-1].nonbitset)
#define CGEN_ATTR_CGEN_HW_VIRTUAL_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_HW_VIRTUAL)) != 0)
#define CGEN_ATTR_CGEN_HW_CACHE_ADDR_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_HW_CACHE_ADDR)) != 0)
#define CGEN_ATTR_CGEN_HW_PC_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_HW_PC)) != 0)
#define CGEN_ATTR_CGEN_HW_PROFILE_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_HW_PROFILE)) != 0)

/* Enum declaration for nds32 hardware types.  */
typedef enum cgen_hw_type {
  HW_H_MEMORY, HW_H_SINT, HW_H_UINT, HW_H_ADDR
 , HW_H_IADDR, HW_H_PC, HW_H_PPC, HW_H_SI
 , HW_H_UIMM5, HW_H_MASK4, HW_H_SWID15, HW_H_DISP24
 , HW_H_CONCAT24, HW_H_DISP16, HW_H_DISP9, HW_H_DISP14
 , HW_H_UHI20, HW_H_SLO20, HW_H_ULO15, HW_H_SLO15
 , HW_H_USR, HW_H_GROUP, HW_H_SR10, HW_H_TPC
 , HW_H_GR, HW_H_SR, HW_H_RESET_SR, HW_H_WTMSK_SR
 , HW_H_CONF_SR, HW_H_ACCUM_HL, HW_H_ACCUM, HW_H_MFUSRIDX
 , HW_H_MTUSRIDX, HW_H_STANDBYST, HW_H_TLBOPST, HW_H_CCTLST
 , HW_H_CCTLLVL, HW_H_MSYNCST, HW_H_DPREFST, HW_H_UIMM3
 , HW_H_ULO3W, HW_H_ULO3H, HW_H_ULO3B, HW_H_SIMM5H
 , HW_H_UIMM5H, HW_H_ULO7W, HW_H_SWID5, HW_H_SWID9
 , HW_H_ITB, HW_H_CONF_ITB, HW_H_WTMSK_ITB, HW_H_HSDISP8
 , HW_H_GR16, HW_H_GR8, HW_H_GR8E5, HW_H_XLSB
 , HW_H_SIMM10H, HW_H_UIMM3_10, HW_H_SIMM5W, HW_H_SUIMM5
 , HW_H_UIMM5D, HW_H_UIMM6W, HW_H_REGLIST, HW_H_EVEN_GR
 , HW_H_SLO19, HW_H_SLO18, HW_H_SLO17, HW_H_DISP8
 , HW_H_SLO11, HW_H_ULO5, HW_H_AR_I, HW_H_AR_M
 , HW_H_AR_MOD, HW_H_CONF_AR_MOD, HW_H_WTMSK_AR_MOD, HW_H_AR_ADM_VBASE
 , HW_H_CONF_AR_ADM_VBASE, HW_H_WTMSK_AR_ADM_VBASE, HW_H_AR_LB, HW_H_AR_LE
 , HW_H_AR_LC, HW_H_AR_CB_CTL, HW_H_WTMSK_AR_CB_CTL, HW_H_AR_SHFT_CTL
 , HW_H_WTMSK_AR_SHFT_CTL, HW_H_AR_CBB, HW_H_WTMSK_AR_CBB, HW_H_AR_CBE
 , HW_H_WTMSK_AR_CBE, HW_H_ACCUM_L24, HW_H_GR_EVEN, HW_H_GR_ODD
 , HW_H_GR_LO, HW_H_GR_LO_EVEN, HW_H_GR_LO_ODD, HW_H_AR_ACCUM
 , HW_H_AR_ACCUM1, HW_H_GR_BOTTOM, HW_H_GR_TOP, HW_H_GR_LO_BOTTOM
 , HW_H_GR_LO_TOP, HW_H_AR_I_LO, HW_H_AR_I_HI, HW_H_AR_M_LO
 , HW_H_AR_M_HI, HW_H_AI_IMM16, HW_H_AI_LSBLOC, HW_H_AI_RC4
 , HW_H_AI_M2_5, HW_H_AI_IM1_4, HW_H_AI_M2_3, HW_H_AI_I2_1
 , HW_H_AI_C1_15, HW_H_AI_RA4_19, HW_H_AI_RB3_14, HW_H_AI_RC2_11
 , HW_H_AI_RC1_5, HW_H_AI_ARIDX4, HW_H_AI_ARIDX5, HW_H_AI_AR2IDX5
 , HW_H_SLO12, HW_H_CONF_FPCFG, HW_H_FCSR, HW_H_CONF_FCSR
 , HW_H_WTMSK_FCSR, HW_H_FSR, HW_H_FDR, HW_H_UIMM19
 , HW_H_UIMM12, HW_H_UIMM2, HW_H_COP0_DR, HW_H_COP0_WR
 , HW_H_COP1_DR, HW_H_COP1_WR, HW_H_COP2_DR, HW_H_COP2_WR
 , HW_H_COP3_DR, HW_H_COP3_WR, HW_H_UIMM8_S, HW_H_IFC_LP
 , HW_H_CONF_IFC_LP, HW_H_WTMSK_IFC_LP, HW_MAX
} CGEN_HW_TYPE;

#define MAX_HW ((int) HW_MAX)

/* Operand attribute indices.  */

/* Enum declaration for cgen_operand attrs.  */
typedef enum cgen_operand_attr {
  CGEN_OPERAND_VIRTUAL, CGEN_OPERAND_PCREL_ADDR, CGEN_OPERAND_ABS_ADDR, CGEN_OPERAND_SIGN_OPT
 , CGEN_OPERAND_SIGNED, CGEN_OPERAND_NEGATIVE, CGEN_OPERAND_RELAX, CGEN_OPERAND_SEM_ONLY
 , CGEN_OPERAND_RELOC, CGEN_OPERAND_HASH_PREFIX, CGEN_OPERAND_END_BOOLS, CGEN_OPERAND_START_NBOOLS = 31
 , CGEN_OPERAND_MACH, CGEN_OPERAND_END_NBOOLS
} CGEN_OPERAND_ATTR;

/* Number of non-boolean elements in cgen_operand_attr.  */
#define CGEN_OPERAND_NBOOL_ATTRS (CGEN_OPERAND_END_NBOOLS - CGEN_OPERAND_START_NBOOLS - 1)

/* cgen_operand attribute accessor macros.  */
#define CGEN_ATTR_CGEN_OPERAND_MACH_VALUE(attrs) ((attrs)->nonbool[CGEN_OPERAND_MACH-CGEN_OPERAND_START_NBOOLS-1].nonbitset)
#define CGEN_ATTR_CGEN_OPERAND_VIRTUAL_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_VIRTUAL)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_PCREL_ADDR_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_PCREL_ADDR)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_ABS_ADDR_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_ABS_ADDR)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_SIGN_OPT_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_SIGN_OPT)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_SIGNED_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_SIGNED)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_NEGATIVE_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_NEGATIVE)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_RELAX_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_RELAX)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_SEM_ONLY_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_SEM_ONLY)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_RELOC_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_RELOC)) != 0)
#define CGEN_ATTR_CGEN_OPERAND_HASH_PREFIX_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_OPERAND_HASH_PREFIX)) != 0)

/* Enum declaration for nds32 operand types.  */
typedef enum cgen_operand_type {
  NDS32_OPERAND_PC, NDS32_OPERAND_RT5, NDS32_OPERAND_RA5, NDS32_OPERAND_RB5
 , NDS32_OPERAND_RD1, NDS32_OPERAND_RD1HL, NDS32_OPERAND_USRIDX, NDS32_OPERAND_GROUPIDX
 , NDS32_OPERAND_MFUSRIDX, NDS32_OPERAND_MTUSRIDX, NDS32_OPERAND_SR10, NDS32_OPERAND_DISP24
 , NDS32_OPERAND_CONCAT24, NDS32_OPERAND_DISP16, NDS32_OPERAND_DISP9, NDS32_OPERAND_DISP14
 , NDS32_OPERAND_TLBOPST, NDS32_OPERAND_CCTLST, NDS32_OPERAND_CCTLLVL, NDS32_OPERAND_MSYNCST
 , NDS32_OPERAND_DPREFST, NDS32_OPERAND_STANDBYST, NDS32_OPERAND_HASH, NDS32_OPERAND_SI
 , NDS32_OPERAND_UIMM5, NDS32_OPERAND_MASK4, NDS32_OPERAND_SWID15, NDS32_OPERAND_UHI20
 , NDS32_OPERAND_SLO20, NDS32_OPERAND_ULO15D, NDS32_OPERAND_SLO15D, NDS32_OPERAND_ULO15W
 , NDS32_OPERAND_SLO15W, NDS32_OPERAND_ULO15H, NDS32_OPERAND_SLO15H, NDS32_OPERAND_ULO15B
 , NDS32_OPERAND_SLO15B, NDS32_OPERAND_ULO15, NDS32_OPERAND_SLO15, NDS32_OPERAND_UIMM_SR10
 , NDS32_OPERAND_RT5H, NDS32_OPERAND_RA5H, NDS32_OPERAND_RB5H, NDS32_OPERAND_RT4
 , NDS32_OPERAND_RA4, NDS32_OPERAND_RT3, NDS32_OPERAND_RT3E5, NDS32_OPERAND_RT3_7
 , NDS32_OPERAND_RA3, NDS32_OPERAND_RB3, NDS32_OPERAND_BITS, NDS32_OPERAND_UIMM3
 , NDS32_OPERAND_ULO3W, NDS32_OPERAND_ULO3H, NDS32_OPERAND_ULO3B, NDS32_OPERAND_SIMM5H
 , NDS32_OPERAND_UIMM5H, NDS32_OPERAND_IMM5U, NDS32_OPERAND_ULO7W, NDS32_OPERAND_SWID5
 , NDS32_OPERAND_SWID9, NDS32_OPERAND_HSDISP8, NDS32_OPERAND_SIMM10, NDS32_OPERAND_RT5E
 , NDS32_OPERAND_RA5E, NDS32_OPERAND_REGLIST, NDS32_OPERAND_UIMM3_10, NDS32_OPERAND_SIMM5W
 , NDS32_OPERAND_SUIMM5, NDS32_OPERAND_UIMM5D, NDS32_OPERAND_UIMM6W, NDS32_OPERAND_SLO19
 , NDS32_OPERAND_SLO18H, NDS32_OPERAND_SLO17W, NDS32_OPERAND_RS5, NDS32_OPERAND_DISP8
 , NDS32_OPERAND_SIMM11, NDS32_OPERAND_ULO5, NDS32_OPERAND_RA5_A, NDS32_OPERAND_RA5_A_B
 , NDS32_OPERAND_RA5_A_T, NDS32_OPERAND_RD5_A, NDS32_OPERAND_ARIDX4_A, NDS32_OPERAND_DH2_16_A
 , NDS32_OPERAND_RB5_A, NDS32_OPERAND_RB5_A_B, NDS32_OPERAND_RB5_A_T, NDS32_OPERAND_RB5P_A
 , NDS32_OPERAND_RB5P_A_B, NDS32_OPERAND_RB5P_A_T, NDS32_OPERAND_D1_A, NDS32_OPERAND_DH2_6_A
 , NDS32_OPERAND_ARIDX5_A, NDS32_OPERAND_AR2IDX5_A, NDS32_OPERAND_LSBLOC_A, NDS32_OPERAND_RC4_A
 , NDS32_OPERAND_M2_5_A, NDS32_OPERAND_IM1_4_A, NDS32_OPERAND_M2_3_A, NDS32_OPERAND_I2_1_A
 , NDS32_OPERAND_C1_15_A, NDS32_OPERAND_RA4_19_A, NDS32_OPERAND_RB3_14_A, NDS32_OPERAND_RC2_11_A
 , NDS32_OPERAND_RC1_5_A, NDS32_OPERAND_RC5_0_A, NDS32_OPERAND_RC5_1_A, NDS32_OPERAND_IM5_I_A
 , NDS32_OPERAND_IM5_M_A, NDS32_OPERAND_IM6_I_0_A, NDS32_OPERAND_IM6_I_1_A, NDS32_OPERAND_IM6_M_0_A
 , NDS32_OPERAND_IM6_M_1_A, NDS32_OPERAND_R10A5_A, NDS32_OPERAND_R10B5_A, NDS32_OPERAND_R10C5_A
 , NDS32_OPERAND_R10A5_A_B, NDS32_OPERAND_R10A5_A_T, NDS32_OPERAND_R10B5_A_B, NDS32_OPERAND_R10B5_A_T
 , NDS32_OPERAND_R10C5_0_A, NDS32_OPERAND_R10C5_1_A, NDS32_OPERAND_IMM16_A, NDS32_OPERAND_FSRT5
 , NDS32_OPERAND_FSRA5, NDS32_OPERAND_FSRB5, NDS32_OPERAND_FDRT5, NDS32_OPERAND_FDRA5
 , NDS32_OPERAND_FDRB5, NDS32_OPERAND_RTH5, NDS32_OPERAND_RTL5, NDS32_OPERAND_SLO12W
 , NDS32_OPERAND_SLO12D, NDS32_OPERAND_UIMM19, NDS32_OPERAND_UIMM12, NDS32_OPERAND_CPID
 , NDS32_OPERAND_CPID2, NDS32_OPERAND_COPDR, NDS32_OPERAND_COPWR, NDS32_OPERAND_UIMM8_S
 , NDS32_OPERAND_MAX
} CGEN_OPERAND_TYPE;

/* Number of operands types.  */
#define MAX_OPERANDS 140

/* Maximum number of operands referenced by any insn.  */
#define MAX_OPERAND_INSTANCES 17

/* Insn attribute indices.  */

/* Enum declaration for cgen_insn attrs.  */
typedef enum cgen_insn_attr {
  CGEN_INSN_ALIAS, CGEN_INSN_VIRTUAL, CGEN_INSN_UNCOND_CTI, CGEN_INSN_COND_CTI
 , CGEN_INSN_SKIP_CTI, CGEN_INSN_DELAY_SLOT, CGEN_INSN_RELAXABLE, CGEN_INSN_RELAXED
 , CGEN_INSN_NO_DIS, CGEN_INSN_PBB, CGEN_INSN_EXT, CGEN_INSN_EXT2
 , CGEN_INSN_A16, CGEN_INSN_A16V2, CGEN_INSN_A32V2, CGEN_INSN_STAT
 , CGEN_INSN_IFCEXT, CGEN_INSN_COP, CGEN_INSN_COPV2, CGEN_INSN_FPU_SP
 , CGEN_INSN_FPU_DP, CGEN_INSN_FPU_COM, CGEN_INSN_FPU_BOTH, CGEN_INSN_FPU_SP_MAC
 , CGEN_INSN_FPU_DP_MAC, CGEN_INSN_STRING, CGEN_INSN_MAC, CGEN_INSN_DX_REG
 , CGEN_INSN_DIV, CGEN_INSN_AUDIO, CGEN_INSN_V3, CGEN_INSN_NOT_V3M
 , CGEN_INSN_END_BOOLS, CGEN_INSN_START_NBOOLS = 31, CGEN_INSN_MACH, CGEN_INSN_PIPE
 , CGEN_INSN_END_NBOOLS
} CGEN_INSN_ATTR;

/* Number of non-boolean elements in cgen_insn_attr.  */
#define CGEN_INSN_NBOOL_ATTRS (CGEN_INSN_END_NBOOLS - CGEN_INSN_START_NBOOLS - 1)

/* cgen_insn attribute accessor macros.  */
#define CGEN_ATTR_CGEN_INSN_MACH_VALUE(attrs) ((attrs)->nonbool[CGEN_INSN_MACH-CGEN_INSN_START_NBOOLS-1].nonbitset)
#define CGEN_ATTR_CGEN_INSN_PIPE_VALUE(attrs) ((attrs)->nonbool[CGEN_INSN_PIPE-CGEN_INSN_START_NBOOLS-1].nonbitset)
#define CGEN_ATTR_CGEN_INSN_ALIAS_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_ALIAS)) != 0)
#define CGEN_ATTR_CGEN_INSN_VIRTUAL_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_VIRTUAL)) != 0)
#define CGEN_ATTR_CGEN_INSN_UNCOND_CTI_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_UNCOND_CTI)) != 0)
#define CGEN_ATTR_CGEN_INSN_COND_CTI_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_COND_CTI)) != 0)
#define CGEN_ATTR_CGEN_INSN_SKIP_CTI_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_SKIP_CTI)) != 0)
#define CGEN_ATTR_CGEN_INSN_DELAY_SLOT_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_DELAY_SLOT)) != 0)
#define CGEN_ATTR_CGEN_INSN_RELAXABLE_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_RELAXABLE)) != 0)
#define CGEN_ATTR_CGEN_INSN_RELAXED_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_RELAXED)) != 0)
#define CGEN_ATTR_CGEN_INSN_NO_DIS_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_NO_DIS)) != 0)
#define CGEN_ATTR_CGEN_INSN_PBB_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_PBB)) != 0)
#define CGEN_ATTR_CGEN_INSN_EXT_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_EXT)) != 0)
#define CGEN_ATTR_CGEN_INSN_EXT2_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_EXT2)) != 0)
#define CGEN_ATTR_CGEN_INSN_A16_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_A16)) != 0)
#define CGEN_ATTR_CGEN_INSN_A16V2_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_A16V2)) != 0)
#define CGEN_ATTR_CGEN_INSN_A32V2_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_A32V2)) != 0)
#define CGEN_ATTR_CGEN_INSN_STAT_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_STAT)) != 0)
#define CGEN_ATTR_CGEN_INSN_IFCEXT_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_IFCEXT)) != 0)
#define CGEN_ATTR_CGEN_INSN_COP_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_COP)) != 0)
#define CGEN_ATTR_CGEN_INSN_COPV2_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_COPV2)) != 0)
#define CGEN_ATTR_CGEN_INSN_FPU_SP_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_FPU_SP)) != 0)
#define CGEN_ATTR_CGEN_INSN_FPU_DP_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_FPU_DP)) != 0)
#define CGEN_ATTR_CGEN_INSN_FPU_COM_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_FPU_COM)) != 0)
#define CGEN_ATTR_CGEN_INSN_FPU_BOTH_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_FPU_BOTH)) != 0)
#define CGEN_ATTR_CGEN_INSN_FPU_SP_MAC_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_FPU_SP_MAC)) != 0)
#define CGEN_ATTR_CGEN_INSN_FPU_DP_MAC_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_FPU_DP_MAC)) != 0)
#define CGEN_ATTR_CGEN_INSN_STRING_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_STRING)) != 0)
#define CGEN_ATTR_CGEN_INSN_MAC_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_MAC)) != 0)
#define CGEN_ATTR_CGEN_INSN_DX_REG_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_DX_REG)) != 0)
#define CGEN_ATTR_CGEN_INSN_DIV_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_DIV)) != 0)
#define CGEN_ATTR_CGEN_INSN_AUDIO_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_AUDIO)) != 0)
#define CGEN_ATTR_CGEN_INSN_V3_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_V3)) != 0)
#define CGEN_ATTR_CGEN_INSN_NOT_V3M_VALUE(attrs) (((attrs)->bool_ & (1 << CGEN_INSN_NOT_V3M)) != 0)

/* cgen.h uses things we just defined.  */
#include "opcode/cgen.h"

extern const struct cgen_ifld nds32_cgen_ifld_table[];

/* Attributes.  */
extern const CGEN_ATTR_TABLE nds32_cgen_hardware_attr_table[];
extern const CGEN_ATTR_TABLE nds32_cgen_ifield_attr_table[];
extern const CGEN_ATTR_TABLE nds32_cgen_operand_attr_table[];
extern const CGEN_ATTR_TABLE nds32_cgen_insn_attr_table[];

/* Hardware decls.  */

extern CGEN_KEYWORD nds32_cgen_opval_gr_names;
extern CGEN_KEYWORD nds32_cgen_opval_sr_names;
extern CGEN_KEYWORD nds32_cgen_opval_sr_names;
extern CGEN_KEYWORD nds32_cgen_opval_sr_names;
extern CGEN_KEYWORD nds32_cgen_opval_sr_names;
extern CGEN_KEYWORD nds32_cgen_opval_accum_hl_names;
extern CGEN_KEYWORD nds32_cgen_opval_accum_names;
extern CGEN_KEYWORD nds32_cgen_opval_h_mfusridx;
extern CGEN_KEYWORD nds32_cgen_opval_h_mtusridx;
extern CGEN_KEYWORD nds32_cgen_opval_h_standbyst;
extern CGEN_KEYWORD nds32_cgen_opval_h_tlbopst;
extern CGEN_KEYWORD nds32_cgen_opval_h_cctlst;
extern CGEN_KEYWORD nds32_cgen_opval_h_cctllvl;
extern CGEN_KEYWORD nds32_cgen_opval_h_msyncst;
extern CGEN_KEYWORD nds32_cgen_opval_h_dprefst;
extern CGEN_KEYWORD nds32_cgen_opval_gr_names_16;
extern CGEN_KEYWORD nds32_cgen_opval_gr_names_8;
extern CGEN_KEYWORD nds32_cgen_opval_gr_names_8e5;
extern CGEN_KEYWORD nds32_cgen_opval_h_xlsb;
extern CGEN_KEYWORD nds32_cgen_opval_h_reglist;
extern CGEN_KEYWORD nds32_cgen_opval_even_gr_names_16;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_i;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_m;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_shft_ctl;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_cbb;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_cbe;
extern CGEN_KEYWORD nds32_cgen_opval_h_accum_l24;
extern CGEN_KEYWORD nds32_cgen_opval_h_gr_even;
extern CGEN_KEYWORD nds32_cgen_opval_h_gr_odd;
extern CGEN_KEYWORD nds32_cgen_opval_h_gr_lo;
extern CGEN_KEYWORD nds32_cgen_opval_h_gr_lo_even;
extern CGEN_KEYWORD nds32_cgen_opval_h_gr_lo_odd;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_accum;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_accum1;
extern CGEN_KEYWORD nds32_cgen_opval_gr_names;
extern CGEN_KEYWORD nds32_cgen_opval_gr_names;
extern CGEN_KEYWORD nds32_cgen_opval_h_gr_lo_bottom;
extern CGEN_KEYWORD nds32_cgen_opval_h_gr_lo_top;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_i_lo;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_i_hi;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_m_lo;
extern CGEN_KEYWORD nds32_cgen_opval_h_ar_m_hi;
extern CGEN_KEYWORD nds32_cgen_opval_h_ai_aridx4;
extern CGEN_KEYWORD nds32_cgen_opval_h_ai_aridx5;
extern CGEN_KEYWORD nds32_cgen_opval_h_ai_ar2idx5;
extern CGEN_KEYWORD nds32_cgen_opval_fcsr_names;
extern CGEN_KEYWORD nds32_cgen_opval_fcsr_names;
extern CGEN_KEYWORD nds32_cgen_opval_fcsr_names;
extern CGEN_KEYWORD nds32_cgen_opval_fsr_names;
extern CGEN_KEYWORD nds32_cgen_opval_h_fdr;
extern CGEN_KEYWORD nds32_cgen_opval_cpr_names;
extern CGEN_KEYWORD nds32_cgen_opval_cpr_names;
extern CGEN_KEYWORD nds32_cgen_opval_cpr_names;
extern CGEN_KEYWORD nds32_cgen_opval_cpr_names;
extern CGEN_KEYWORD nds32_cgen_opval_cpr_names;
extern CGEN_KEYWORD nds32_cgen_opval_cpr_names;
extern CGEN_KEYWORD nds32_cgen_opval_cpr_names;
extern CGEN_KEYWORD nds32_cgen_opval_cpr_names;

extern const CGEN_HW_ENTRY nds32_cgen_hw_table[];



#endif /* NDS32_CPU_H */
