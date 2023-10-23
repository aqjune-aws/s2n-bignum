(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC
 *)

(* ========================================================================= *)
(* Extended Montgomery reduction of arbitrary bignum.                        *)
(* ========================================================================= *)

(**** print_literal_from_elf "arm/fastmul/bignum_emontredc_8n_neon.o";;
 ****)

let bignum_emontredc_8n_neon_mc =
  define_assert_from_elf "bignum_emontredc_8n_neon_mc" "arm/fastmul/bignum_emontredc_8n_neon.o"
[
  0xd10383ff;       (* arm_SUB SP SP (rvalue (word 224)) *)
  0xa90d53f3;       (* arm_STP X19 X20 SP (Immediate_Offset (iword (&208))) *)
  0xa90c5bf5;       (* arm_STP X21 X22 SP (Immediate_Offset (iword (&192))) *)
  0xa90b63f7;       (* arm_STP X23 X24 SP (Immediate_Offset (iword (&176))) *)
  0xa90a6bf9;       (* arm_STP X25 X26 SP (Immediate_Offset (iword (&160))) *)
  0xa90973fb;       (* arm_STP X27 X28 SP (Immediate_Offset (iword (&144))) *)
  0xa9087bfd;       (* arm_STP X29 X30 SP (Immediate_Offset (iword (&128))) *)
  0x3d8003e8;       (* arm_STR Q8 SP (Immediate_Offset (word 0)) *)
  0x3d8007e9;       (* arm_STR Q9 SP (Immediate_Offset (word 16)) *)
  0x3d800bea;       (* arm_STR Q10 SP (Immediate_Offset (word 32)) *)
  0x3d800feb;       (* arm_STR Q11 SP (Immediate_Offset (word 48)) *)
  0x3d8013ec;       (* arm_STR Q12 SP (Immediate_Offset (word 64)) *)
  0x3d8017ed;       (* arm_STR Q13 SP (Immediate_Offset (word 80)) *)
  0x3d801bee;       (* arm_STR Q14 SP (Immediate_Offset (word 96)) *)
  0x3d801fef;       (* arm_STR Q15 SP (Immediate_Offset (word 112)) *)
  0xd10183ff;       (* arm_SUB SP SP (rvalue (word 96)) *)
  0xd10083ff;       (* arm_SUB SP SP (rvalue (word 32)) *)
  0xd342fc00;       (* arm_LSR X0 X0 2 *)
  0xaa0003fa;       (* arm_MOV X26 X0 *)
  0xf100040c;       (* arm_SUBS X12 X0 (rvalue (word 1)) *)
  0x54004203;       (* arm_BCC (word 2112) *)
  0xaa0403f8;       (* arm_MOV X24 X4 *)
  0xaa0403fe;       (* arm_MOV X30 X4 *)
  0xaa0203f9;       (* arm_MOV X25 X2 *)
  0xaa0c03fb;       (* arm_MOV X27 X12 *)
  0xa9c21444;       (* arm_LDP X4 X5 X2 (Preimmediate_Offset (iword (&32))) *)
  0xa9411c46;       (* arm_LDP X6 X7 X2 (Immediate_Offset (iword (&16))) *)
  0xeb0400bc;       (* arm_SUBS X28 X5 X4 *)
  0xda9c279c;       (* arm_CNEG X28 X28 Condition_CC *)
  0xda9f23fd;       (* arm_CSETM X29 Condition_CC *)
  0xa90077dc;       (* arm_STP X28 X29 X30 (Immediate_Offset (iword (&0))) *)
  0xeb0400dc;       (* arm_SUBS X28 X6 X4 *)
  0xda9c279c;       (* arm_CNEG X28 X28 Condition_CC *)
  0xda9f23fd;       (* arm_CSETM X29 Condition_CC *)
  0xa90177dc;       (* arm_STP X28 X29 X30 (Immediate_Offset (iword (&16))) *)
  0xeb0400fc;       (* arm_SUBS X28 X7 X4 *)
  0xda9c279c;       (* arm_CNEG X28 X28 Condition_CC *)
  0xda9f23fd;       (* arm_CSETM X29 Condition_CC *)
  0xa90277dc;       (* arm_STP X28 X29 X30 (Immediate_Offset (iword (&32))) *)
  0xeb0500dc;       (* arm_SUBS X28 X6 X5 *)
  0xda9c279c;       (* arm_CNEG X28 X28 Condition_CC *)
  0xda9f23fd;       (* arm_CSETM X29 Condition_CC *)
  0xa90377dc;       (* arm_STP X28 X29 X30 (Immediate_Offset (iword (&48))) *)
  0xeb0500fc;       (* arm_SUBS X28 X7 X5 *)
  0xda9c279c;       (* arm_CNEG X28 X28 Condition_CC *)
  0xda9f23fd;       (* arm_CSETM X29 Condition_CC *)
  0xa90477dc;       (* arm_STP X28 X29 X30 (Immediate_Offset (iword (&64))) *)
  0xeb0600fc;       (* arm_SUBS X28 X7 X6 *)
  0xda9c279c;       (* arm_CNEG X28 X28 Condition_CC *)
  0xda9f23fd;       (* arm_CSETM X29 Condition_CC *)
  0xa90577dc;       (* arm_STP X28 X29 X30 (Immediate_Offset (iword (&80))) *)
  0x910183de;       (* arm_ADD X30 X30 (rvalue (word 96)) *)
  0xf100077b;       (* arm_SUBS X27 X27 (rvalue (word 1)) *)
  0xb5fffc9b;       (* arm_CBNZ X27 (word 2097040) *)
  0xaa1903e2;       (* arm_MOV X2 X25 *)
  0xaa1803fe;       (* arm_MOV X30 X24 *)
  0xa9007be3;       (* arm_STP X3 X30 SP (Immediate_Offset (iword (&0))) *)
  0xa9017ffa;       (* arm_STP X26 XZR SP (Immediate_Offset (iword (&16))) *)
  0xaa1f03fc;       (* arm_MOV X28 XZR *)
  0xd37be980;       (* arm_LSL X0 X12 5 *)
  0x6f00e5fd;       (* arm_MOVI Q29 (word 4294967295) *)
  0xa9403429;       (* arm_LDP X9 X13 X1 (Immediate_Offset (iword (&0))) *)
  0xf94003e3;       (* arm_LDR X3 SP (Immediate_Offset (word 0)) *)
  0xd345fc1b;       (* arm_LSR X27 X0 5 *)
  0xd100077b;       (* arm_SUB X27 X27 (rvalue (word 1)) *)
  0xa941302a;       (* arm_LDP X10 X12 X1 (Immediate_Offset (iword (&16))) *)
  0xa9403c44;       (* arm_LDP X4 X15 X2 (Immediate_Offset (iword (&0))) *)
  0x3dc00441;       (* arm_LDR Q1 X2 (Immediate_Offset (word 16)) *)
  0x9b037d2b;       (* arm_MUL X11 X9 X3 *)
  0x4e815832;       (* arm_UZP2 Q18 Q1 Q1 32 *)
  0x4e080d7b;       (* arm_DUP_GEN Q27 X11 *)
  0x0ea1282d;       (* arm_XTN Q13 Q1 32 *)
  0x4ea00829;       (* arm_REV64_VEC Q9 Q1 32 *)
  0x9b047d67;       (* arm_MUL X7 X11 X4 *)
  0x4ea00822;       (* arm_REV64_VEC Q2 Q1 32 *)
  0x4e815834;       (* arm_UZP2 Q20 Q1 Q1 32 *)
  0x4ebb9d3f;       (* arm_MUL_VEC Q31 Q9 Q27 32 *)
  0x0ea1282e;       (* arm_XTN Q14 Q1 32 *)
  0x4e815835;       (* arm_UZP2 Q21 Q1 Q1 32 *)
  0x9bcf7d76;       (* arm_UMULH X22 X11 X15 *)
  0x0ea12b71;       (* arm_XTN Q17 Q27 32 *)
  0xab070133;       (* arm_ADDS X19 X9 X7 *)
  0x2eadc23c;       (* arm_UMULL_VEC Q28 Q17 Q13 32 *)
  0x2eb2c23a;       (* arm_UMULL_VEC Q26 Q17 Q18 32 *)
  0x6ea02be8;       (* arm_UADDLP Q8 Q31 32 *)
  0x9bc47d68;       (* arm_UMULH X8 X11 X4 *)
  0x4f605507;       (* arm_SHL_VEC Q7 Q8 32 64 *)
  0x4e9b5b7e;       (* arm_UZP2 Q30 Q27 Q27 32 *)
  0x2ead8227;       (* arm_UMLAL_VEC Q7 Q17 Q13 32 *)
  0x9b0f7d6e;       (* arm_MUL X14 X11 X15 *)
  0x6f60179a;       (* arm_USRA_VEC Q26 Q28 32 64 128 *)
  0x2eb2c3cc;       (* arm_UMULL_VEC Q12 Q30 Q18 32 *)
  0x4e083cf8;       (* arm_UMOV X24 Q7 0 8 *)
  0xba0e01bd;       (* arm_ADCS X29 X13 X14 *)
  0x4e3d1f44;       (* arm_AND_VEC Q4 Q26 Q29 128 *)
  0x4e183cf1;       (* arm_UMOV X17 Q7 1 8 *)
  0x4ea0083b;       (* arm_REV64_VEC Q27 Q1 32 *)
  0xba180145;       (* arm_ADCS X5 X10 X24 *)
  0x2ead83c4;       (* arm_UMLAL_VEC Q4 Q30 Q13 32 *)
  0x6f60174c;       (* arm_USRA_VEC Q12 Q26 32 64 128 *)
  0xba11018e;       (* arm_ADCS X14 X12 X17 *)
  0x9a1f03f7;       (* arm_ADC X23 XZR XZR *)
  0xab0803a8;       (* arm_ADDS X8 X29 X8 *)
  0xba1600a7;       (* arm_ADCS X7 X5 X22 *)
  0x9b037d19;       (* arm_MUL X25 X8 X3 *)
  0x6f60148c;       (* arm_USRA_VEC Q12 Q4 32 64 128 *)
  0x4e080f28;       (* arm_DUP_GEN Q8 X25 *)
  0xa900642b;       (* arm_STP X11 X25 X1 (Immediate_Offset (iword (&0))) *)
  0x9b047f36;       (* arm_MUL X22 X25 X4 *)
  0x4e183d90;       (* arm_UMOV X16 Q12 1 8 *)
  0x3dc00030;       (* arm_LDR Q16 X1 (Immediate_Offset (word 0)) *)
  0x4e083d95;       (* arm_UMOV X21 Q12 0 8 *)
  0x4ea89f7f;       (* arm_MUL_VEC Q31 Q27 Q8 32 *)
  0xba1501d4;       (* arm_ADCS X20 X14 X21 *)
  0x0ea1291b;       (* arm_XTN Q27 Q8 32 *)
  0x9a1002ea;       (* arm_ADC X10 X23 X16 *)
  0xeb19016e;       (* arm_SUBS X14 X11 X25 *)
  0x4ea00a11;       (* arm_REV64_VEC Q17 Q16 32 *)
  0xda8e25d1;       (* arm_CNEG X17 X14 Condition_CC *)
  0xda9f23fa;       (* arm_CSETM X26 Condition_CC *)
  0x6ea02bfa;       (* arm_UADDLP Q26 Q31 32 *)
  0x9b0f7f26;       (* arm_MUL X6 X25 X15 *)
  0xa9026bf1;       (* arm_STP X17 X26 SP (Immediate_Offset (iword (&32))) *)
  0x2eaec378;       (* arm_UMULL_VEC Q24 Q27 Q14 32 *)
  0x4e905a1e;       (* arm_UZP2 Q30 Q16 Q16 32 *)
  0x4f605744;       (* arm_SHL_VEC Q4 Q26 32 64 *)
  0x4e885905;       (* arm_UZP2 Q5 Q8 Q8 32 *)
  0x9bc47f31;       (* arm_UMULH X17 X25 X4 *)
  0x2eae8364;       (* arm_UMLAL_VEC Q4 Q27 Q14 32 *)
  0x2eb5c368;       (* arm_UMULL_VEC Q8 Q27 Q21 32 *)
  0x4e083c95;       (* arm_UMOV X21 Q4 0 8 *)
  0xab160108;       (* arm_ADDS X8 X8 X22 *)
  0x4e183c8c;       (* arm_UMOV X12 Q4 1 8 *)
  0xa9413857;       (* arm_LDP X23 X14 X2 (Immediate_Offset (iword (&16))) *)
  0xba0600fd;       (* arm_ADCS X29 X7 X6 *)
  0x9bcf7f2d;       (* arm_UMULH X13 X25 X15 *)
  0x6f601708;       (* arm_USRA_VEC Q8 Q24 32 64 128 *)
  0xa94163c8;       (* arm_LDP X8 X24 X30 (Immediate_Offset (iword (&16))) *)
  0xba150289;       (* arm_ADCS X9 X20 X21 *)
  0x3cc20c49;       (* arm_LDR Q9 X2 (Preimmediate_Offset (iword (&32))) *)
  0x0ea12a1c;       (* arm_XTN Q28 Q16 32 *)
  0xba0c0153;       (* arm_ADCS X19 X10 X12 *)
  0x3dc0044d;       (* arm_LDR Q13 X2 (Immediate_Offset (word 16)) *)
  0x2eb5c0b2;       (* arm_UMULL_VEC Q18 Q5 Q21 32 *)
  0x9a1f03e7;       (* arm_ADC X7 XZR XZR *)
  0xab1103a5;       (* arm_ADDS X5 X29 X17 *)
  0x0ea12835;       (* arm_XTN Q21 Q1 32 *)
  0x9b037cac;       (* arm_MUL X12 X5 X3 *)
  0x4e3d1d04;       (* arm_AND_VEC Q4 Q8 Q29 128 *)
  0xba0d0135;       (* arm_ADCS X21 X9 X13 *)
  0x4e89593f;       (* arm_UZP2 Q31 Q9 Q9 32 *)
  0x0ea12937;       (* arm_XTN Q23 Q9 32 *)
  0x6f601512;       (* arm_USRA_VEC Q18 Q8 32 64 128 *)
  0x2eae80a4;       (* arm_UMLAL_VEC Q4 Q5 Q14 32 *)
  0x4e080d85;       (* arm_DUP_GEN Q5 X12 *)
  0x2ebec2f0;       (* arm_UMULL_VEC Q16 Q23 Q30 32 *)
  0x2ebcc2e1;       (* arm_UMULL_VEC Q1 Q23 Q28 32 *)
  0x9bcf7d9d;       (* arm_UMULH X29 X12 X15 *)
  0x2ebec3e8;       (* arm_UMULL_VEC Q8 Q31 Q30 32 *)
  0x0ea129b8;       (* arm_XTN Q24 Q13 32 *)
  0x4ea59c59;       (* arm_MUL_VEC Q25 Q2 Q5 32 *)
  0x6f601492;       (* arm_USRA_VEC Q18 Q4 32 64 128 *)
  0x0ea128a3;       (* arm_XTN Q3 Q5 32 *)
  0x4e8558b3;       (* arm_UZP2 Q19 Q5 Q5 32 *)
  0x9b0f7d8a;       (* arm_MUL X10 X12 X15 *)
  0x2eb4c07a;       (* arm_UMULL_VEC Q26 Q3 Q20 32 *)
  0x4e083e56;       (* arm_UMOV X22 Q18 0 8 *)
  0x2eb5c06a;       (* arm_UMULL_VEC Q10 Q3 Q21 32 *)
  0x6ea02b2b;       (* arm_UADDLP Q11 Q25 32 *)
  0x4e183e46;       (* arm_UMOV X6 Q18 1 8 *)
  0x9b047d90;       (* arm_MUL X16 X12 X4 *)
  0x2eb4c264;       (* arm_UMULL_VEC Q4 Q19 Q20 32 *)
  0x6f601430;       (* arm_USRA_VEC Q16 Q1 32 64 128 *)
  0xba16026d;       (* arm_ADCS X13 X19 X22 *)
  0x4f60556b;       (* arm_SHL_VEC Q11 Q11 32 64 *)
  0x9a0600e6;       (* arm_ADC X6 X7 X6 *)
  0xeb0c0167;       (* arm_SUBS X7 X11 X12 *)
  0x6f60155a;       (* arm_USRA_VEC Q26 Q10 32 64 128 *)
  0xda9f23fa;       (* arm_CSETM X26 Condition_CC *)
  0xda8724f4;       (* arm_CNEG X20 X7 Condition_CC *)
  0xeb0c0333;       (* arm_SUBS X19 X25 X12 *)
  0x2eb5806b;       (* arm_UMLAL_VEC Q11 Q3 Q21 32 *)
  0xda932669;       (* arm_CNEG X9 X19 Condition_CC *)
  0xa9036bf4;       (* arm_STP X20 X26 SP (Immediate_Offset (iword (&48))) *)
  0x9bc47d87;       (* arm_UMULH X7 X12 X4 *)
  0x6f601608;       (* arm_USRA_VEC Q8 Q16 32 64 128 *)
  0x4ea99e27;       (* arm_MUL_VEC Q7 Q17 Q9 32 *)
  0xda9f23fa;       (* arm_CSETM X26 Condition_CC *)
  0xab1000b3;       (* arm_ADDS X19 X5 X16 *)
  0x4e3d1e01;       (* arm_AND_VEC Q1 Q16 Q29 128 *)
  0xba0a02b5;       (* arm_ADCS X21 X21 X10 *)
  0xa9056be9;       (* arm_STP X9 X26 SP (Immediate_Offset (iword (&80))) *)
  0xa94353f1;       (* arm_LDP X17 X20 SP (Immediate_Offset (iword (&48))) *)
  0x6f601744;       (* arm_USRA_VEC Q4 Q26 32 64 128 *)
  0x4e3d1f52;       (* arm_AND_VEC Q18 Q26 Q29 128 *)
  0x2ebc83e1;       (* arm_UMLAL_VEC Q1 Q31 Q28 32 *)
  0x4e083d76;       (* arm_UMOV X22 Q11 0 8 *)
  0x4e183d70;       (* arm_UMOV X16 Q11 1 8 *)
  0x2eb58272;       (* arm_UMLAL_VEC Q18 Q19 Q21 32 *)
  0xba1601b3;       (* arm_ADCS X19 X13 X22 *)
  0x9b087e36;       (* arm_MUL X22 X17 X8 *)
  0x6ea028e5;       (* arm_UADDLP Q5 Q7 32 *)
  0xba1000cd;       (* arm_ADCS X13 X6 X16 *)
  0x6f601428;       (* arm_USRA_VEC Q8 Q1 32 64 128 *)
  0x9a1f03e9;       (* arm_ADC X9 XZR XZR *)
  0xab0702a5;       (* arm_ADDS X5 X21 X7 *)
  0x6f601644;       (* arm_USRA_VEC Q4 Q18 32 64 128 *)
  0xba1d0266;       (* arm_ADCS X6 X19 X29 *)
  0x9b037cb3;       (* arm_MUL X19 X5 X3 *)
  0x4f6054af;       (* arm_SHL_VEC Q15 Q5 32 64 *)
  0x4e183d03;       (* arm_UMOV X3 Q8 1 8 *)
  0x2ebc82ef;       (* arm_UMLAL_VEC Q15 Q23 Q28 32 *)
  0x4e083c95;       (* arm_UMOV X21 Q4 0 8 *)
  0x9b177e67;       (* arm_MUL X7 X19 X23 *)
  0xa9014c2c;       (* arm_STP X12 X19 X1 (Immediate_Offset (iword (&16))) *)
  0x4e183c8a;       (* arm_UMOV X10 Q4 1 8 *)
  0x3dc00429;       (* arm_LDR Q9 X1 (Immediate_Offset (word 16)) *)
  0xba1501ad;       (* arm_ADCS X13 X13 X21 *)
  0x4e183df5;       (* arm_UMOV X21 Q15 1 8 *)
  0x9b047e70;       (* arm_MUL X16 X19 X4 *)
  0x9a0a0129;       (* arm_ADC X9 X9 X10 *)
  0xeb13033d;       (* arm_SUBS X29 X25 X19 *)
  0xda9f23fa;       (* arm_CSETM X26 Condition_CC *)
  0xda9d27aa;       (* arm_CNEG X10 X29 Condition_CC *)
  0xeb13019d;       (* arm_SUBS X29 X12 X19 *)
  0xa9066bea;       (* arm_STP X10 X26 SP (Immediate_Offset (iword (&96))) *)
  0x4e895932;       (* arm_UZP2 Q18 Q9 Q9 32 *)
  0x9b0f7e6c;       (* arm_MUL X12 X19 X15 *)
  0x4ea00934;       (* arm_REV64_VEC Q20 Q9 32 *)
  0x0ea12933;       (* arm_XTN Q19 Q9 32 *)
  0x2eb2c319;       (* arm_UMULL_VEC Q25 Q24 Q18 32 *)
  0xda9f23fa;       (* arm_CSETM X26 Condition_CC *)
  0x2eb3c30e;       (* arm_UMULL_VEC Q14 Q24 Q19 32 *)
  0xda9d27bd;       (* arm_CNEG X29 X29 Condition_CC *)
  0x9bd77e6a;       (* arm_UMULH X10 X19 X23 *)
  0xab1000b9;       (* arm_ADDS X25 X5 X16 *)
  0x4ead9e87;       (* arm_MUL_VEC Q7 Q20 Q13 32 *)
  0xba0c00cc;       (* arm_ADCS X12 X6 X12 *)
  0xa94217e6;       (* arm_LDP X6 X5 SP (Immediate_Offset (iword (&32))) *)
  0x4e083d10;       (* arm_UMOV X16 Q8 0 8 *)
  0xba0701b9;       (* arm_ADCS X25 X13 X7 *)
  0xa9076bfd;       (* arm_STP X29 X26 SP (Immediate_Offset (iword (&112))) *)
  0x6f6015d9;       (* arm_USRA_VEC Q25 Q14 32 64 128 *)
  0x9b0e7e7d;       (* arm_MUL X29 X19 X14 *)
  0x4e8d59a1;       (* arm_UZP2 Q1 Q13 Q13 32 *)
  0x6ea028e7;       (* arm_UADDLP Q7 Q7 32 *)
  0x2eb2c020;       (* arm_UMULL_VEC Q0 Q1 Q18 32 *)
  0x9bc47e6d;       (* arm_UMULH X13 X19 X4 *)
  0x4e3d1f2a;       (* arm_AND_VEC Q10 Q25 Q29 128 *)
  0x4f6054ed;       (* arm_SHL_VEC Q13 Q7 32 64 *)
  0xba1d0124;       (* arm_ADCS X4 X9 X29 *)
  0x2eb3802a;       (* arm_UMLAL_VEC Q10 Q1 Q19 32 *)
  0x9a1f03e9;       (* arm_ADC X9 XZR XZR *)
  0xeb13017d;       (* arm_SUBS X29 X11 X19 *)
  0x6f601720;       (* arm_USRA_VEC Q0 Q25 32 64 128 *)
  0xca18028b;       (* arm_EOR X11 X20 X24 *)
  0x9bcf7e6f;       (* arm_UMULH X15 X19 X15 *)
  0x2eb3830d;       (* arm_UMLAL_VEC Q13 Q24 Q19 32 *)
  0xda9d27a7;       (* arm_CNEG X7 X29 Condition_CC *)
  0xa9c27434;       (* arm_LDP X20 X29 X1 (Preimmediate_Offset (iword (&32))) *)
  0xda9f23fa;       (* arm_CSETM X26 Condition_CC *)
  0x6f601540;       (* arm_USRA_VEC Q0 Q10 32 64 128 *)
  0x9bce7e73;       (* arm_UMULH X19 X19 X14 *)
  0x4e183db7;       (* arm_UMOV X23 Q13 1 8 *)
  0xa9046be7;       (* arm_STP X7 X26 SP (Immediate_Offset (iword (&64))) *)
  0xab0d018c;       (* arm_ADDS X12 X12 X13 *)
  0xba0f032d;       (* arm_ADCS X13 X25 X15 *)
  0x4e083c1a;       (* arm_UMOV X26 Q0 0 8 *)
  0x9bc87e28;       (* arm_UMULH X8 X17 X8 *)
  0xba0a008e;       (* arm_ADCS X14 X4 X10 *)
  0x4e083db1;       (* arm_UMOV X17 Q13 0 8 *)
  0x9a13012f;       (* arm_ADC X15 X9 X19 *)
  0xa8c62bd8;       (* arm_LDP X24 X10 X30 (Postimmediate_Offset (iword (&96))) *)
  0x3cc20c4e;       (* arm_LDR Q14 X2 (Preimmediate_Offset (iword (&32))) *)
  0x3dc00459;       (* arm_LDR Q25 X2 (Immediate_Offset (word 16)) *)
  0xca0a00b3;       (* arm_EOR X19 X5 X10 *)
  0xab1002b9;       (* arm_ADDS X25 X21 X16 *)
  0x4e183c10;       (* arm_UMOV X16 Q0 1 8 *)
  0xa9411c24;       (* arm_LDP X4 X7 X1 (Immediate_Offset (iword (&16))) *)
  0xba030235;       (* arm_ADCS X21 X17 X3 *)
  0xca0b02d6;       (* arm_EOR X22 X22 X11 *)
  0xba1a02f7;       (* arm_ADCS X23 X23 X26 *)
  0x9a1f0211;       (* arm_ADC X17 X16 XZR *)
  0xab140190;       (* arm_ADDS X16 X12 X20 *)
  0x9b187cc5;       (* arm_MUL X5 X6 X24 *)
  0x0ea129d5;       (* arm_XTN Q21 Q14 32 *)
  0x0ea12b3f;       (* arm_XTN Q31 Q25 32 *)
  0xba1d01a9;       (* arm_ADCS X9 X13 X29 *)
  0x4e995b38;       (* arm_UZP2 Q24 Q25 Q25 32 *)
  0x4e083dfd;       (* arm_UMOV X29 Q15 0 8 *)
  0xba0401c4;       (* arm_ADCS X4 X14 X4 *)
  0xa94737ea;       (* arm_LDP X10 X13 SP (Immediate_Offset (iword (&112))) *)
  0x2ebec2a5;       (* arm_UMULL_VEC Q5 Q21 Q30 32 *)
  0x9bd87cd4;       (* arm_UMULH X20 X6 X24 *)
  0xba0701f8;       (* arm_ADCS X24 X15 X7 *)
  0xa97f1fcc;       (* arm_LDP X12 X7 X30 (Immediate_Offset (iword (-- &16))) *)
  0x2eb2c3f0;       (* arm_UMULL_VEC Q16 Q31 Q18 32 *)
  0x9a1f03e6;       (* arm_ADC X6 XZR XZR *)
  0xab1d032e;       (* arm_ADDS X14 X25 X29 *)
  0x2ebcc2ad;       (* arm_UMULL_VEC Q13 Q21 Q28 32 *)
  0x4e8e59ca;       (* arm_UZP2 Q10 Q14 Q14 32 *)
  0xca0b010f;       (* arm_EOR X15 X8 X11 *)
  0xba1902b9;       (* arm_ADCS X25 X21 X25 *)
  0x2eb3c3e1;       (* arm_UMULL_VEC Q1 Q31 Q19 32 *)
  0xba1502e8;       (* arm_ADCS X8 X23 X21 *)
  0x4eb99e86;       (* arm_MUL_VEC Q6 Q20 Q25 32 *)
  0xca0701a7;       (* arm_EOR X7 X13 X7 *)
  0xba170237;       (* arm_ADCS X23 X17 X23 *)
  0xca1300b5;       (* arm_EOR X21 X5 X19 *)
  0x9a1103ed;       (* arm_ADC X13 XZR X17 *)
  0xab1d0331;       (* arm_ADDS X17 X25 X29 *)
  0x2eb2c300;       (* arm_UMULL_VEC Q0 Q24 Q18 32 *)
  0x6f6015a5;       (* arm_USRA_VEC Q5 Q13 32 64 128 *)
  0xba0e0105;       (* arm_ADCS X5 X8 X14 *)
  0x2ebec142;       (* arm_UMULL_VEC Q2 Q10 Q30 32 *)
  0xba1902f9;       (* arm_ADCS X25 X23 X25 *)
  0x6f601430;       (* arm_USRA_VEC Q16 Q1 32 64 128 *)
  0xba0801a8;       (* arm_ADCS X8 X13 X8 *)
  0x6ea028cd;       (* arm_UADDLP Q13 Q6 32 *)
  0xba1703f7;       (* arm_ADCS X23 XZR X23 *)
  0x4e3d1ca7;       (* arm_AND_VEC Q7 Q5 Q29 128 *)
  0x9a0d03ed;       (* arm_ADC X13 XZR X13 *)
  0xab1003bd;       (* arm_ADDS X29 X29 X16 *)
  0x9b0c7d50;       (* arm_MUL X16 X10 X12 *)
  0x6f6014a2;       (* arm_USRA_VEC Q2 Q5 32 64 128 *)
  0xba0901c9;       (* arm_ADCS X9 X14 X9 *)
  0x4e3d1e19;       (* arm_AND_VEC Q25 Q16 Q29 128 *)
  0xba040231;       (* arm_ADCS X17 X17 X4 *)
  0x2ebc8147;       (* arm_UMLAL_VEC Q7 Q10 Q28 32 *)
  0x9bcc7d4c;       (* arm_UMULH X12 X10 X12 *)
  0xba1800aa;       (* arm_ADCS X10 X5 X24 *)
  0x6f601600;       (* arm_USRA_VEC Q0 Q16 32 64 128 *)
  0xca070205;       (* arm_EOR X5 X16 X7 *)
  0xa97e3bd0;       (* arm_LDP X16 X14 X30 (Immediate_Offset (iword (-- &32))) *)
  0xba060326;       (* arm_ADCS X6 X25 X6 *)
  0x4f6055b0;       (* arm_SHL_VEC Q16 Q13 32 64 *)
  0xca130298;       (* arm_EOR X24 X20 X19 *)
  0xba1f0104;       (* arm_ADCS X4 X8 XZR *)
  0xa94667f4;       (* arm_LDP X20 X25 SP (Immediate_Offset (iword (&96))) *)
  0x2eb38319;       (* arm_UMLAL_VEC Q25 Q24 Q19 32 *)
  0xba1f02f7;       (* arm_ADCS X23 X23 XZR *)
  0x6f6014e2;       (* arm_USRA_VEC Q2 Q7 32 64 128 *)
  0x2eb383f0;       (* arm_UMLAL_VEC Q16 Q31 Q19 32 *)
  0x9a1f01a8;       (* arm_ADC X8 X13 XZR *)
  0xb10004ff;       (* arm_CMN X7 (rvalue (word 1)) *)
  0x4eae9e27;       (* arm_MUL_VEC Q7 Q17 Q14 32 *)
  0xba050084;       (* arm_ADCS X4 X4 X5 *)
  0xca070185;       (* arm_EOR X5 X12 X7 *)
  0xba0502f7;       (* arm_ADCS X23 X23 X5 *)
  0x9b107e8c;       (* arm_MUL X12 X20 X16 *)
  0x9a070105;       (* arm_ADC X5 X8 X7 *)
  0xb100067f;       (* arm_CMN X19 (rvalue (word 1)) *)
  0xba150135;       (* arm_ADCS X21 X9 X21 *)
  0xca0e0328;       (* arm_EOR X8 X25 X14 *)
  0x6f601720;       (* arm_USRA_VEC Q0 Q25 32 64 128 *)
  0xba18022d;       (* arm_ADCS X13 X17 X24 *)
  0xa900543d;       (* arm_STP X29 X21 X1 (Immediate_Offset (iword (&0))) *)
  0x9bd07e94;       (* arm_UMULH X20 X20 X16 *)
  0x6ea028ea;       (* arm_UADDLP Q10 Q7 32 *)
  0xba130151;       (* arm_ADCS X17 X10 X19 *)
  0x4e183c43;       (* arm_UMOV X3 Q2 1 8 *)
  0xa94463fd;       (* arm_LDP X29 X24 SP (Immediate_Offset (iword (&64))) *)
  0xba1300d9;       (* arm_ADCS X25 X6 X19 *)
  0xa97c57c6;       (* arm_LDP X6 X21 X30 (Immediate_Offset (iword (-- &64))) *)
  0xca08018a;       (* arm_EOR X10 X12 X8 *)
  0xba130089;       (* arm_ADCS X9 X4 X19 *)
  0x4e083c1a;       (* arm_UMOV X26 Q0 0 8 *)
  0xa97d43c4;       (* arm_LDP X4 X16 X30 (Immediate_Offset (iword (-- &48))) *)
  0xba1302ec;       (* arm_ADCS X12 X23 X19 *)
  0x9a1300a5;       (* arm_ADC X5 X5 X19 *)
  0xb100051f;       (* arm_CMN X8 (rvalue (word 1)) *)
  0xa9454fe7;       (* arm_LDP X7 X19 SP (Immediate_Offset (iword (&80))) *)
  0xba0a032e;       (* arm_ADCS X14 X25 X10 *)
  0x9b067fb9;       (* arm_MUL X25 X29 X6 *)
  0xca080294;       (* arm_EOR X20 X20 X8 *)
  0xba140137;       (* arm_ADCS X23 X9 X20 *)
  0xa94353e9;       (* arm_LDP X9 X20 SP (Immediate_Offset (iword (&48))) *)
  0xca150318;       (* arm_EOR X24 X24 X21 *)
  0xba08018c;       (* arm_ADCS X12 X12 X8 *)
  0x9a0800aa;       (* arm_ADC X10 X5 X8 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0x9bc67fa5;       (* arm_UMULH X5 X29 X6 *)
  0x4f60554f;       (* arm_SHL_VEC Q15 Q10 32 64 *)
  0xba1601a8;       (* arm_ADCS X8 X13 X22 *)
  0xca18032d;       (* arm_EOR X13 X25 X24 *)
  0xba0f023d;       (* arm_ADCS X29 X17 X15 *)
  0x2ebc82af;       (* arm_UMLAL_VEC Q15 Q21 Q28 32 *)
  0xba0b01d6;       (* arm_ADCS X22 X14 X11 *)
  0x4e083e11;       (* arm_UMOV X17 Q16 0 8 *)
  0xba0b02f5;       (* arm_ADCS X21 X23 X11 *)
  0x9b047cf7;       (* arm_MUL X23 X7 X4 *)
  0xba0b018e;       (* arm_ADCS X14 X12 X11 *)
  0xca10026c;       (* arm_EOR X12 X19 X16 *)
  0x4e083c50;       (* arm_UMOV X16 Q2 0 8 *)
  0x9a0b014f;       (* arm_ADC X15 X10 X11 *)
  0xb100071f;       (* arm_CMN X24 (rvalue (word 1)) *)
  0xca1800b3;       (* arm_EOR X19 X5 X24 *)
  0xba0d03ab;       (* arm_ADCS X11 X29 X13 *)
  0x9bc47cfd;       (* arm_UMULH X29 X7 X4 *)
  0xba1302cd;       (* arm_ADCS X13 X22 X19 *)
  0xa94217e6;       (* arm_LDP X6 X5 SP (Immediate_Offset (iword (&32))) *)
  0xa94167c7;       (* arm_LDP X7 X25 X30 (Immediate_Offset (iword (&16))) *)
  0xba1802b3;       (* arm_ADCS X19 X21 X24 *)
  0x4e183df5;       (* arm_UMOV X21 Q15 1 8 *)
  0xca0c02f6;       (* arm_EOR X22 X23 X12 *)
  0xba1801ce;       (* arm_ADCS X14 X14 X24 *)
  0x4e183e17;       (* arm_UMOV X23 Q16 1 8 *)
  0x9a1801ef;       (* arm_ADC X15 X15 X24 *)
  0xb100059f;       (* arm_CMN X12 (rvalue (word 1)) *)
  0xa8c62bd8;       (* arm_LDP X24 X10 X30 (Postimmediate_Offset (iword (&96))) *)
  0xba16016b;       (* arm_ADCS X11 X11 X22 *)
  0x9b077d36;       (* arm_MUL X22 X9 X7 *)
  0xca0c03a4;       (* arm_EOR X4 X29 X12 *)
  0xba0401a4;       (* arm_ADCS X4 X13 X4 *)
  0xa9012c28;       (* arm_STP X8 X11 X1 (Immediate_Offset (iword (&16))) *)
  0xba0c026d;       (* arm_ADCS X13 X19 X12 *)
  0xca19028b;       (* arm_EOR X11 X20 X25 *)
  0xa9c27434;       (* arm_LDP X20 X29 X1 (Preimmediate_Offset (iword (&32))) *)
  0xba0c01ce;       (* arm_ADCS X14 X14 X12 *)
  0x9a0c01ef;       (* arm_ADC X15 X15 X12 *)
  0xaa0403ec;       (* arm_MOV X12 X4 *)
  0x9bc77d28;       (* arm_UMULH X8 X9 X7 *)
  0xd100077b;       (* arm_SUB X27 X27 (rvalue (word 1)) *)
  0xb5ffed5b;       (* arm_CBNZ X27 (word 2096552) *)
  0x9bd87cd3;       (* arm_UMULH X19 X6 X24 *)
  0xa94727e7;       (* arm_LDP X7 X9 SP (Immediate_Offset (iword (&112))) *)
  0xab1002a4;       (* arm_ADDS X4 X21 X16 *)
  0x4e183c19;       (* arm_UMOV X25 Q0 1 8 *)
  0xca0a00a5;       (* arm_EOR X5 X5 X10 *)
  0xba030231;       (* arm_ADCS X17 X17 X3 *)
  0xa9412830;       (* arm_LDP X16 X10 X1 (Immediate_Offset (iword (&16))) *)
  0xba1a02f5;       (* arm_ADCS X21 X23 X26 *)
  0xca0b0108;       (* arm_EOR X8 X8 X11 *)
  0x9a1f0337;       (* arm_ADC X23 X25 XZR *)
  0xab140194;       (* arm_ADDS X20 X12 X20 *)
  0xba1d01ac;       (* arm_ADCS X12 X13 X29 *)
  0x4e083df9;       (* arm_UMOV X25 Q15 0 8 *)
  0xba1001cd;       (* arm_ADCS X13 X14 X16 *)
  0xca050270;       (* arm_EOR X16 X19 X5 *)
  0xba0a01fd;       (* arm_ADCS X29 X15 X10 *)
  0xa97f4fce;       (* arm_LDP X14 X19 X30 (Immediate_Offset (iword (-- &16))) *)
  0x9b187ccf;       (* arm_MUL X15 X6 X24 *)
  0x9a1f03f8;       (* arm_ADC X24 XZR XZR *)
  0xab190086;       (* arm_ADDS X6 X4 X25 *)
  0xba04022a;       (* arm_ADCS X10 X17 X4 *)
  0xca0b02c4;       (* arm_EOR X4 X22 X11 *)
  0xba1102b1;       (* arm_ADCS X17 X21 X17 *)
  0xca130136;       (* arm_EOR X22 X9 X19 *)
  0xba1502e9;       (* arm_ADCS X9 X23 X21 *)
  0x9a1703f5;       (* arm_ADC X21 XZR X23 *)
  0xab190157;       (* arm_ADDS X23 X10 X25 *)
  0xca0501ef;       (* arm_EOR X15 X15 X5 *)
  0xba060233;       (* arm_ADCS X19 X17 X6 *)
  0xa9417ffa;       (* arm_LDP X26 XZR SP (Immediate_Offset (iword (&16))) *)
  0xcb000042;       (* arm_SUB X2 X2 X0 *)
  0xba0a012a;       (* arm_ADCS X10 X9 X10 *)
  0xba1102b1;       (* arm_ADCS X17 X21 X17 *)
  0xba0903e9;       (* arm_ADCS X9 XZR X9 *)
  0x9a1503f5;       (* arm_ADC X21 XZR X21 *)
  0xab140339;       (* arm_ADDS X25 X25 X20 *)
  0x9b0e7cf4;       (* arm_MUL X20 X7 X14 *)
  0xba0c00c6;       (* arm_ADCS X6 X6 X12 *)
  0xba0d02f7;       (* arm_ADCS X23 X23 X13 *)
  0xba1d026d;       (* arm_ADCS X13 X19 X29 *)
  0x9bce7cf3;       (* arm_UMULH X19 X7 X14 *)
  0xa97e77ce;       (* arm_LDP X14 X29 X30 (Immediate_Offset (iword (-- &32))) *)
  0xba18014a;       (* arm_ADCS X10 X10 X24 *)
  0xa9461fec;       (* arm_LDP X12 X7 SP (Immediate_Offset (iword (&96))) *)
  0xba1f0231;       (* arm_ADCS X17 X17 XZR *)
  0xba1f0138;       (* arm_ADCS X24 X9 XZR *)
  0x9a1f02a9;       (* arm_ADC X9 X21 XZR *)
  0xb10006df;       (* arm_CMN X22 (rvalue (word 1)) *)
  0xca160295;       (* arm_EOR X21 X20 X22 *)
  0xba150234;       (* arm_ADCS X20 X17 X21 *)
  0xca160271;       (* arm_EOR X17 X19 X22 *)
  0x9b0e7d93;       (* arm_MUL X19 X12 X14 *)
  0xca1d00fd;       (* arm_EOR X29 X7 X29 *)
  0xba110311;       (* arm_ADCS X17 X24 X17 *)
  0x9a160129;       (* arm_ADC X9 X9 X22 *)
  0xb10004bf;       (* arm_CMN X5 (rvalue (word 1)) *)
  0x9bce7d95;       (* arm_UMULH X21 X12 X14 *)
  0xa94463ee;       (* arm_LDP X14 X24 SP (Immediate_Offset (iword (&64))) *)
  0xba0f00c6;       (* arm_ADCS X6 X6 X15 *)
  0xba1002e7;       (* arm_ADCS X7 X23 X16 *)
  0xa97c33cf;       (* arm_LDP X15 X12 X30 (Immediate_Offset (iword (-- &64))) *)
  0xca1d0273;       (* arm_EOR X19 X19 X29 *)
  0xba0501ad;       (* arm_ADCS X13 X13 X5 *)
  0xa9001839;       (* arm_STP X25 X6 X1 (Immediate_Offset (iword (&0))) *)
  0xba050150;       (* arm_ADCS X16 X10 X5 *)
  0xa97d1bca;       (* arm_LDP X10 X6 X30 (Immediate_Offset (iword (-- &48))) *)
  0xba050297;       (* arm_ADCS X23 X20 X5 *)
  0xba050239;       (* arm_ADCS X25 X17 X5 *)
  0x9bcf7dde;       (* arm_UMULH X30 X14 X15 *)
  0xa9455bf1;       (* arm_LDP X17 X22 SP (Immediate_Offset (iword (&80))) *)
  0x9a050129;       (* arm_ADC X9 X9 X5 *)
  0xb10007bf;       (* arm_CMN X29 (rvalue (word 1)) *)
  0xca1d02b5;       (* arm_EOR X21 X21 X29 *)
  0xba130210;       (* arm_ADCS X16 X16 X19 *)
  0xba1502e5;       (* arm_ADCS X5 X23 X21 *)
  0xca0c0317;       (* arm_EOR X23 X24 X12 *)
  0x9b0a7e2c;       (* arm_MUL X12 X17 X10 *)
  0xba1d0333;       (* arm_ADCS X19 X25 X29 *)
  0x9a1d013d;       (* arm_ADC X29 X9 X29 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xba0400e7;       (* arm_ADCS X7 X7 X4 *)
  0xba0801b5;       (* arm_ADCS X21 X13 X8 *)
  0x9b0f7dc4;       (* arm_MUL X4 X14 X15 *)
  0xca1703c9;       (* arm_EOR X9 X30 X23 *)
  0xba0b021e;       (* arm_ADCS X30 X16 X11 *)
  0xba0b00b8;       (* arm_ADCS X24 X5 X11 *)
  0xba0b0270;       (* arm_ADCS X16 X19 X11 *)
  0x9a0b03b3;       (* arm_ADC X19 X29 X11 *)
  0xb10006ff;       (* arm_CMN X23 (rvalue (word 1)) *)
  0xca170088;       (* arm_EOR X8 X4 X23 *)
  0xba0802a4;       (* arm_ADCS X4 X21 X8 *)
  0x9bca7e35;       (* arm_UMULH X21 X17 X10 *)
  0xba0903c8;       (* arm_ADCS X8 X30 X9 *)
  0xa942782a;       (* arm_LDP X10 X30 X1 (Immediate_Offset (iword (&32))) *)
  0xba170319;       (* arm_ADCS X25 X24 X23 *)
  0xca0602cb;       (* arm_EOR X11 X22 X6 *)
  0xba170216;       (* arm_ADCS X22 X16 X23 *)
  0xca0b0185;       (* arm_EOR X5 X12 X11 *)
  0x9a17027d;       (* arm_ADC X29 X19 X23 *)
  0xb100057f;       (* arm_CMN X11 (rvalue (word 1)) *)
  0xca0b02ae;       (* arm_EOR X14 X21 X11 *)
  0xba050089;       (* arm_ADCS X9 X4 X5 *)
  0xa9012427;       (* arm_STP X7 X9 X1 (Immediate_Offset (iword (&16))) *)
  0xba0e0109;       (* arm_ADCS X9 X8 X14 *)
  0xba0b0333;       (* arm_ADCS X19 X25 X11 *)
  0xa9435428;       (* arm_LDP X8 X21 X1 (Immediate_Offset (iword (&48))) *)
  0xaa0903f8;       (* arm_MOV X24 X9 *)
  0xba0b02c5;       (* arm_ADCS X5 X22 X11 *)
  0x9a0b03b0;       (* arm_ADC X16 X29 X11 *)
  0xab1c039f;       (* arm_CMN X28 X28 *)
  0xba180151;       (* arm_ADCS X17 X10 X24 *)
  0xba1303ce;       (* arm_ADCS X14 X30 X19 *)
  0xf94007fe;       (* arm_LDR X30 SP (Immediate_Offset (word 8)) *)
  0xba050108;       (* arm_ADCS X8 X8 X5 *)
  0xa9023831;       (* arm_STP X17 X14 X1 (Immediate_Offset (iword (&32))) *)
  0xba1002a9;       (* arm_ADCS X9 X21 X16 *)
  0xda9f33fc;       (* arm_CSETM X28 Condition_CS *)
  0xa9032428;       (* arm_STP X8 X9 X1 (Immediate_Offset (iword (&48))) *)
  0xf100075a;       (* arm_SUBS X26 X26 (rvalue (word 1)) *)
  0xcb000021;       (* arm_SUB X1 X1 X0 *)
  0xa9017ffa;       (* arm_STP X26 XZR SP (Immediate_Offset (iword (&16))) *)
  0x91008021;       (* arm_ADD X1 X1 (rvalue (word 32)) *)
  0x54ffc361;       (* arm_BNE (word 2095212) *)
  0xcb1c03e0;       (* arm_NEG X0 X28 *)
  0x910083ff;       (* arm_ADD SP SP (rvalue (word 32)) *)
  0x910183ff;       (* arm_ADD SP SP (rvalue (word 96)) *)
  0x3dc003e8;       (* arm_LDR Q8 SP (Immediate_Offset (word 0)) *)
  0x3dc007e9;       (* arm_LDR Q9 SP (Immediate_Offset (word 16)) *)
  0x3dc00bea;       (* arm_LDR Q10 SP (Immediate_Offset (word 32)) *)
  0x3dc00feb;       (* arm_LDR Q11 SP (Immediate_Offset (word 48)) *)
  0x3dc013ec;       (* arm_LDR Q12 SP (Immediate_Offset (word 64)) *)
  0x3dc017ed;       (* arm_LDR Q13 SP (Immediate_Offset (word 80)) *)
  0x3dc01bee;       (* arm_LDR Q14 SP (Immediate_Offset (word 96)) *)
  0x3dc01fef;       (* arm_LDR Q15 SP (Immediate_Offset (word 112)) *)
  0xa9487bfd;       (* arm_LDP X29 X30 SP (Immediate_Offset (iword (&128))) *)
  0xa94973fb;       (* arm_LDP X27 X28 SP (Immediate_Offset (iword (&144))) *)
  0xa94a6bf9;       (* arm_LDP X25 X26 SP (Immediate_Offset (iword (&160))) *)
  0xa94b63f7;       (* arm_LDP X23 X24 SP (Immediate_Offset (iword (&176))) *)
  0xa94c5bf5;       (* arm_LDP X21 X22 SP (Immediate_Offset (iword (&192))) *)
  0xa94d53f3;       (* arm_LDP X19 X20 SP (Immediate_Offset (iword (&208))) *)
  0x910383ff;       (* arm_ADD SP SP (rvalue (word 224)) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let BIGNUM_EMONTREDC_8N_NEON_EXEC = ARM_MK_EXEC_RULE bignum_emontredc_8n_neon_mc;;

(* ------------------------------------------------------------------------- *)
(* Proof.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*** Lemma to justify zeros in the Montgomery steps ***)

let montgomery_lemma = prove
 (`!w n.
    (n * w + 1 == 0) (mod (2 EXP 64))
    ==> !h l x.
            &2 pow 64 * &h + &l:real =
            &(val (word(x * w):int64)) *
            &(val(word(bigdigit n 0):int64))
            ==> !h' l'. &2 pow 64 * &h' + &(val l'):real = &x + &l
                        ==> val(l':int64) = 0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN
  REWRITE_TAC[VAL_WORD_ZX_GEN; VAL_WORD; GSYM LOWDIGITS_1; lowdigits] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM VAL_MOD_REFL] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o AP_TERM `\x. x MOD 2 EXP 64`)) THEN
  REWRITE_TAC[MOD_MULT_ADD; DIMINDEX_128; DIMINDEX_64; MULT_CLAUSES] THEN
  REWRITE_TAC[MOD_MOD_EXP_MIN] THEN
  REWRITE_TAC[ARITH_RULE `MIN 64 64 = 64 /\ MIN 128 64 = 64`] THEN
  CONV_TAC MOD_DOWN_CONV THEN REWRITE_TAC[GSYM CONG; GSYM DIVIDES_MOD] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`2 EXP 64`,`p:num`) THEN
  CONV_TAC NUMBER_RULE);;

(*** Lemmas for the case splits in the ADK blocks ***)

let lemma1 = prove
 (`!(x0:num) x1 (y0:num) y1.
       (if y0 <= y1
        then if x1 <= x0 then word 0 else word 18446744073709551615
        else word_not
         (if x1 <= x0 then word 0 else word 18446744073709551615)):int64 =
   word_neg(word(bitval(y0 <= y1 <=> x0 < x1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  CONV_TAC WORD_REDUCE_CONV);;

let lemma2 = prove
 (`!(x0:int64) (x1:int64) (y0:int64) (y1:int64).
        &(val(if val x1 <= val x0 then word_sub x0 x1
              else word_neg (word_sub x0 x1))) *
        &(val(if val y0 <= val y1 then word_sub y1 y0
              else word_neg (word_sub y1 y0))):real =
        --(&1) pow bitval(val y0 <= val y1 <=> val x0 < val x1) *
        (&(val x0) - &(val x1)) * (&(val y1) - &(val y0))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LE; WORD_NEG_SUB] THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES]) THEN
  REPEAT(FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (ARITH_RULE
   `~(m:num <= n) ==> n <= m /\ ~(m <= n)`))) THEN
  ASM_SIMP_TAC[VAL_WORD_SUB_CASES; GSYM REAL_OF_NUM_SUB] THEN
  REAL_ARITH_TAC);;

(*** Load helpful lemmas and tactics for NEONs ***)

needs "arm/proofs/neon_helper.ml";;

(*** Define a few important definitions and useful functions ***)

let inner_loop_invariant = 
  `\i s.  read X1 s = word_sub (word_add z (word(32 * i))) (word 32) /\
          read X2 s = word_sub (word_add m (word(32 * i))) (word 32) /\
          bignum_from_memory(m,k) s = n /\
          read X0 s = word (32 * (k4 - 1)) /\
          read SP s = word_sub stackpointer (word 32) /\
          read (memory :> bytes64 (word_sub stackpointer (word 32))) s = word w /\
          read (memory :>
            bytes64 (word_add (word_sub stackpointer (word 32)) (word 16))) s =
            wouter /\
          read X28 s = word_neg(word cout) /\
          bignum_from_memory (z,4) s = q /\
           read X4 s = word (bigdigit q 0) /\
           read X5 s = word (bigdigit q 1) /\
           read X6 s = word (bigdigit q 2) /\
           read X7 s = word (bigdigit q 3) /\
          bignum_from_memory (word_add z (word (8 * 4 * i)),
                                (k + 4) - 4 * i) s =
              highdigits a (4 * i) /\

          // induction variable
          read X27 s = word (32 * (k4 - i)) /\

          // two vector regs read during outerloop
          read Q20 s = word_join
            (word(bigdigit q 1):(64)word) (word(bigdigit q 0):(64)word) /\
          read Q21 s = word_join
            (word(bigdigit q 3):(64)word) (word(bigdigit q 2):(64)word) /\

          // pre-calculated multiplications
          read X16 s =
            word ((val (word (bigdigit q 0):(64)word) *
                   val (word (bigdigit n (4 * i)):(64)word)) DIV 2 EXP 64):(64)word /\ // hi of x4*x8
          read X26 s = word
            ((val (word (bigdigit q 2):(64)word) *
              val (word (bigdigit n (4 * i + 2)):(64)word)) DIV 2 EXP 64):(64)word /\ // hi of x6 * x10
          read X3 s  = word
            ((val (word (bigdigit q 1):(64)word) *
              val (word (bigdigit n (4 * i + 1)):(64)word)) DIV 2 EXP 64):(64)word /\ // hi of x5 * x9
          read X17 s = word
            ((val (word (bigdigit q 3):(64)word) *
              val (word (bigdigit n (4 * i + 3)):(64)word)) DIV 2 EXP 64):(64)word /\ // hi of x6 * x10
          read X20 s =
            word (0 + val (word (bigdigit q 1):(64)word)
                    * val (word (bigdigit n (4 * i + 1)):(64)word)):(64)word /\ // lo of x5 * x9
          read X21 s =
            word (0 + val (word (bigdigit q 2):(64)word)
                    * val (word (bigdigit n (4 * i + 2)):(64)word)):(64)word /\ // lo of x6 * x10
          read X24 s =
            word (0 + val (word (bigdigit q 3):(64)word)
                    * val (word (bigdigit n (4 * i + 3)):(64)word)):(64)word /\ // lo of x7 * x11
          read Q24 s = word_join
            (word (0 + val (word (bigdigit q 1):(64)word)
                     * val (word (bigdigit n (4 * i + 1)):(64)word)):(64)word)
            (word (0 + val (word (bigdigit q 0):(64)word)
                     * val (word (bigdigit n (4 * i)):(64)word)):(64)word) /\
          ((n * w + 1 == 0) (mod (2 EXP 64))
            ==> 2 EXP (64 * 4 * i) *
                bignum_of_wordlist
                [read X12 s; read X13 s; read X14 s; read X15 s] +
                bignum_from_memory(z,4 * i) s =
                q * lowdigits n (4 * i) + lowdigits a (4 * i) + q)`;;

let inner_loop_invariant_with_flag = mk_abs
  (`i:num`, mk_abs
    (`s:armstate`, mk_conj
      (snd (dest_abs (snd (dest_abs inner_loop_invariant))),
        `read ZF s <=> i = (k4-1)`)));;

(* Given f = \i. x, return x[n/i] *)
let apply_i f n = rhs (concl (BETA_CONV (mk_comb (f, n))));;

let get_hoare_precond (concl:term) =
  try
    let hoare_precond = rand(rator(rator(concl))) in
    hoare_precond
  with Failure _ ->
    failwith ("get_hoare_precond cannot understand " ^ string_of_term concl);;

(* Given a hoare condition that is
   `\s. aligned_bytes_loaded s (word pc) .._mc /\
       read PC s = ... /\
       BODY`,
   return `\s. BODY`. *)
let strip_mc_and_pc_conds (hoare_cond:term):term =
  let s,body = dest_abs hoare_cond in
  let aligned_load_mc, body = dest_conj body in
  let old_pc_eq, body = dest_conj body in
  let old_pc_eq_lhs, old_pc_eq_rhs = dest_eq old_pc_eq in
  if not (old_pc_eq_lhs = `read PC s`) then
    failwith ("Must be `read PC s = ...`, but got " ^ string_of_term old_pc_eq) else
  mk_abs(s, body);;

(* Given a hoare condition that is
   `\s. aligned_bytes_loaded s (word pc) .._mc /\
       read PC s = ... /\
       BODY`,
   return `\s. aligned_bytes_loaded s (word pc) .._mc /\
       read PC s = ... /\
       t /\ BODY`. *)
let mk_hoare_cond_conj (hoare_cond,t:term*term):term =
  let s,body = dest_abs hoare_cond in
  let aligned_load_mc, body = dest_conj body in
  let read_pc, body = dest_conj body in
  mk_abs(s, mk_conj(aligned_load_mc, mk_conj(read_pc, mk_conj(t, body))));;

(* A solver that targets conclusions like this:
    `2 EXP 256 * bignum_of_wordlist [sum_s179; sum_s180; sum_s181; sum_s182] +
    val sum_s53 +
    2 EXP 64 * val sum_s103 +
    2 EXP 128 * val sum_s141 +
    2 EXP 192 * val sum_s174 =
    (val (word (bigdigit q 0)) +
      2 EXP 64 * val (word (bigdigit q 1)) +
      2 EXP 128 * val (word (bigdigit q 2)) +
      2 EXP 192 * val (word (bigdigit q 3))) *
    (2 EXP (64 * 3) * bigdigit n 7 +
      2 EXP (64 * 2) * bigdigit n 6 +
      2 EXP (64 * 1) * bigdigit n 5 +
      bigdigit n 4) +
    2 EXP (64 * 3) * bigdigit a 7 +
    2 EXP (64 * 2) * bigdigit a 6 +
    2 EXP (64 * 1) * bigdigit a 5 +
    bigdigit a 4 +
    bignum_of_wordlist [g8; g9; g10; g11]` *)
let PROVE_IT = REWRITE_TAC[bignum_of_wordlist] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ONCE_REWRITE_TAC[GSYM VAL_WORD_BIGDIGIT] THEN REWRITE_TAC[WORD_VAL] THEN
    MATCH_MP_TAC EQUAL_FROM_CONGRUENT_REAL THEN
    MAP_EVERY EXISTS_TAC [`512`; `&0:real`] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [BOUNDER_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL [REAL_INTEGER_TAC; ALL_TAC] THEN

    ACCUMULATOR_POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      REWRITE_TAC[lemma1; lemma2] THEN REWRITE_TAC[WORD_XOR_MASK] THEN

    REPEAT(COND_CASES_TAC THEN
          ASM_REWRITE_TAC[BITVAL_CLAUSES; REAL_VAL_WORD_NOT]) THEN
    CONV_TAC WORD_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[BITVAL_CLAUSES; DIMINDEX_64] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o DESUM_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[VAL_WORD_BIGDIGIT; ADD_CLAUSES; VAL_WORD_BITVAL] THEN
    CONV_TAC(RAND_CONV REAL_POLY_CONV) THEN
    FIRST_ASSUM(MP_TAC o end_itlist CONJ o filter (is_ratconst o rand o concl) o
              DECARRY_RULE o CONJUNCTS) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    (REAL_INTEGER_TAC ORELSE
      (PRINT_GOAL_TAC "REAL_INTEGER_TAC could not prove this goal" THEN
       FAIL_TAC "REAL_INTEGER failed"));;

(* Add "[T] (comment_NAME)" as an assumption. *)
let COMMENT_TAC s (asl,g) =
  let assumptions_to_remove = List.filter
      (fun (asm_name, _) -> String.starts_with ~prefix:"comment_" asm_name)
      asl in
  (MAP_EVERY (fun asm_name -> REMOVE_THEN asm_name (K ALL_TAC))
      (List.map fst assumptions_to_remove) THEN
   SUBGOAL_THEN `T` (LABEL_TAC ("comment_" ^ s)) THENL [MESON_TAC[]; ALL_TAC]) (asl,g);;

let CHECK_NUM_GOALS (n:int) (msg:string): tactic =
  let all_tacs = replicate ALL_TAC n in
  fun g -> try (ALL_TAC THENL all_tacs) g with
      Failure s ->
        if s = "seqapply: Length mismatch"
        then failwith (Printf.sprintf "# goals != %d! msg: %s" n msg)
        else failwith s;;

let PAIR_EQ_ARITH_RULE (lp,rp:term*term) =
  let lpl,lpr = dest_pair lp in
  let rpl,rpr = dest_pair rp in
  let lth = ARITH_RULE (mk_eq (lpl,rpl)) in
  let rth = ARITH_RULE (mk_eq (lpr,rpr)) in
  let th = REFL lp in
  let th = GEN_REWRITE_RULE (RAND_CONV o LAND_CONV) [lth] th in
  GEN_REWRITE_RULE (RAND_CONV o RAND_CONV) [rth] th;;


let READ_MEMORY_BYTES_0 = prove(`read (memory :> bytes (z,0)) s = 0`,
    REWRITE_TAC[PAIR_EQ_ARITH_RULE (`(x:int64,0)`,`(x:int64, 8*0)`)] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; BIGNUM_FROM_MEMORY_TRIVIAL]);;

let BIGNUM_FROM_MEMORY_DIV2 = prove(`!a d n s.
    bignum_from_memory (word_add a (word (8 * n)),d) s =
    bignum_from_memory (a,d + n) s DIV 2 EXP (64 * n)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[PAIR_EQ_ARITH_RULE
    (`(word_add x y:int64,d:num)`,`(word_add x y:int64,(d+n)-n)`)] THEN
  REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_DIV]);;

(*
        ldp a0, a1, [m, #32]!
        ldp a2, a3, [m, #16]

        cdiff(t, c, a1, a0)
        stp   t, c, [x30, #cache_m10]
        cdiff(t, c, a2, a0)
        stp   t, c, [x30, #cache_m20]
        cdiff(t, c, a3, a0)
        stp   t, c, [x30, #cache_m30]
        cdiff(t, c, a2, a1)
        stp   t, c, [x30, #cache_m21]
        cdiff(t, c, a3, a1)
        stp   t, c, [x30, #cache_m31]
        cdiff(t, c, a3, a2)
        stp   t, c, [x30, #cache_m32]
*)

(* Returns (|x-y|, x-y >= 0) *)
let cdiff (x,y:term*term): term * term =
  let subres = subst [(x,`__t1__:num`);(y,`__t2__:num`)]
      `word_sub (word __t1__) (word __t2__):int64` in
  let cmpres = subst [(x,`__t1__:num`);(y,`__t2__:num`)]
      `val (word __t2__:int64) <= val (word __t1__:int64)` in
  let absdiff = subst [(cmpres,`__isnonneg__:bool`);(subres,`__sub__:int64`)]
      `if __isnonneg__ then (__sub__:int64) else word_neg __sub__` in
  (absdiff, cmpres);;

(* Returns (|d|, d >= 0) where d = n[m_ofs_div_4*4 + i0] - n[m_ofs_div_4*4 + i1] *)
let cdiff_from_bignum (n:term) (m_ofs_div_4:term) (i0:int) (i1:int): term * term =
  assert (type_of m_ofs_div_4 = `:num` && type_of n = `:num`);
  let template = `bigdigit __n__ (__m_ofs_div_4__ * 4 + __idx__)` in
  let operands = [(n,`__n__:num`); (m_ofs_div_4,`__m_ofs_div_4__:num`)] in
  let i0num, i1num = mk_numeral (Int i0), mk_numeral (Int i1) in
  let tfst, tsnd =
    subst ((i0num,`__idx__:num`)::operands) template,
    subst ((i1num,`__idx__:num`)::operands) template in
  cdiff (tfst, tsnd);;

let precalc_bignum_template =
  `val (__absdiff_0__:int64) +
  2 EXP (64 * 1) * val (if __isnonneg_0__ then (word 0) else (word 18446744073709551615):int64) +
  2 EXP (64 * 2) * val (__absdiff_1__:int64) +
  2 EXP (64 * 3) * val (if __isnonneg_1__ then (word 0) else (word 18446744073709551615):int64) +
  2 EXP (64 * 4) * val (__absdiff_2__:int64) +
  2 EXP (64 * 5) * val (if __isnonneg_2__ then (word 0) else (word 18446744073709551615):int64) +
  2 EXP (64 * 6) * val (__absdiff_3__:int64) +
  2 EXP (64 * 7) * val (if __isnonneg_3__ then (word 0) else (word 18446744073709551615):int64) +
  2 EXP (64 * 8) * val (__absdiff_4__:int64) +
  2 EXP (64 * 9) * val (if __isnonneg_4__ then (word 0) else (word 18446744073709551615):int64) +
  2 EXP (64 * 10) * val (__absdiff_5__:int64) +
  2 EXP (64 * 11) * val (if __isnonneg_5__ then (word 0) else (word 18446744073709551615):int64)`;;

(* Precalculated differences and signs of words in modulus *)
let m_precalc_value: thm =
  let full_expr = subst
      (List.concat ((List.mapi (fun i (i0, i1) ->
            let d, isneg = cdiff_from_bignum `n:num` `(i_div_4+1):num` i0 i1 in
            [(d, mk_var(Printf.sprintf "__absdiff_%d__" i,`:int64`));
            (isneg, mk_var(Printf.sprintf "__isnonneg_%d__" i,`:bool`))])
          [(1,0);(2,0);(3,0);(2,1);(3,1);(3,2)])))
      precalc_bignum_template in
  define
    (subst [full_expr,mk_var("__full_expr__",`:num`)]
     `(m_precalc_value (n:num) 0 = 0) /\
      (m_precalc_value (n:num) (i_div_4 + 1) =
            (m_precalc_value n i_div_4) +
            (2 EXP (64 * 12 * i_div_4)) * __full_expr__)`);;

(* Precalculated differences and signs in the current iteration of buffer z *)
let z_precalc_value: thm =
  let full_expr = subst
      (List.concat ((List.mapi (fun i (i0, i1) ->
            let d, isneg = cdiff_from_bignum `z1:num` `0:num` i0 i1 in
            [(d, mk_var(Printf.sprintf "__absdiff_%d__" i,`:int64`));
            (isneg, mk_var(Printf.sprintf "__isnonneg_%d__" i,`:bool`))])
          [(0,1);(0,2);(0,3);(1,2);(1,3);(2,3)])))
      precalc_bignum_template in
  define
    (subst [full_expr,mk_var("__full_expr__",`:num`)]
     `z_precalc_value (z1:num) = (__full_expr__:num)`);;

let VAL_WORD_EQ_ZERO = prove (`!i. i < 2 EXP 64 ==> (val (word i:int64) = 0 <=> i = 0)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
  SUBGOAL_THEN `i MOD 2 EXP 64 = i` (fun thm -> REWRITE_TAC[thm]) THEN IMP_REWRITE_TAC[MOD_LT]);;

let REMOVE_ASSUMS_INCLUDING (the_var:term) =
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (free_in the_var) o concl));;

let erw t = e(REWRITE_TAC[t]);;
let emp t = e(MATCH_MP_TAC t);;

let REWRITE_ATLEASTONCE_CONV (thms:thm list) (t:term) =
  let t' = REWRITE_CONV thms t in
  let lhs,rhs = dest_binary "=" (concl t') in
  if lhs = rhs
  then failwith
    ("REWRITE_ATLEASTONCE_CONV: " ^ (string_of_term t) ^ " cannot be rewritten")
  else t';;

let print_assumptions_including_str (keyword:string) =
  List.iter (fun (hterm:term) ->
    let hthmstr = string_of_term (hterm) in
    if contains_str hthmstr keyword
    then Printf.printf "[%s]\n" hthmstr
    else ()) (fst (top_goal()));;

let ASSERT_READ_BYTES128_EQ_JOIN64_TAC (addr:term) (stname:string): tactic =
  fun (asl,g) ->
    let repls = [(addr,`__addr__:int64`);(mk_var(stname,`:armstate`), `__state__:armstate`)] in
    let lo64read_lhs = subst repls `read (memory :> bytes64 (__addr__)) __state__` in
    let hi64read_lhs = subst repls `read (memory :> bytes64 (word_add __addr__ (word 8))) __state__` in
    let hi64read_lhs = snd (dest_eq (concl
      ((REWRITE_CONV [WORD_ADD_ASSOC_CONSTS] THENC DEPTH_CONV (NUM_ADD_CONV))
       hi64read_lhs))) in
    let choose_eq_from_assum (lhs:term):thm = snd (List.find (fun (_,th) ->
      let t = concl th in is_eq t && (fst (dest_eq t) = lhs)) asl) in
    let lo64_thm = choose_eq_from_assum lo64read_lhs in
    let hi64_thm = choose_eq_from_assum hi64read_lhs in

    let lhs128 = subst repls `read (memory :> bytes128 (__addr__)) __state__` in
    let lo64 = snd (dest_eq (concl lo64_thm)) in
    let hi64 = snd (dest_eq (concl hi64_thm)) in
    let hilo = mk_comb (mk_comb
      (`word_join:(64)word->(64)word->(128)word`,hi64),lo64) in
    (SUBGOAL_THEN (mk_eq (lhs128, hilo)) ASSUME_TAC THENL [
      REWRITE_TAC[GSYM lo64_thm;GSYM hi64_thm;READ_MEMORY_BYTESIZED_SPLIT;
                  WORD_ADD_ASSOC_CONSTS] THEN
      ARITH_TAC;
      ALL_TAC
    ]) (asl,g);;

extra_word_CONV := [
  GEN_REWRITE_CONV I [VAL_WORD_BIGDIGIT;
      WORD_BITMANIP_SIMP_LEMMAS; WORD_MUL64_LO;
      WORD_MUL64_HI]]
  @ (!extra_word_CONV);;

g `!k z m w m_sub_precalc a n pc stackpointer.
        aligned 16 stackpointer /\
        ALLPAIRS nonoverlapping
          [(word pc,LENGTH bignum_emontredc_8n_neon_mc); (m,8 * val k)]
          [(z,8 * 2 * val k); (word_sub stackpointer (word 128), 128);
           (m_sub_precalc,8 * 12 * (val k DIV 4 - 1))] /\
        ALLPAIRS nonoverlapping
          [(z,8 * 2 * val k); (m_sub_precalc,8 * 12 * (val k DIV 4 - 1))]
          [(word_sub stackpointer (word 128), 128)] /\
        nonoverlapping
          (z,8 * 2 * val k) (m_sub_precalc,8 * 12 * (val k DIV 4 - 1)) /\
        8 divides val k /\
        8 * 12 * (val k DIV 4 - 1) < 2 EXP 64
      ==> ensures arm
            (\s. aligned_bytes_loaded s (word pc) bignum_emontredc_8n_neon_mc /\
              read PC s = word(pc + 0x3c) /\
              read SP s = stackpointer /\
              C_ARGUMENTS [k; z; m; w; m_sub_precalc] s /\
              bignum_from_memory (z,2 * val k) s = a /\
              bignum_from_memory (m,val k) s = n)
          (\s. read PC s = word(pc + 0x898) /\
              ((n * val w + 1 == 0) (mod (2 EXP 64))
                ==> n * bignum_from_memory (z,val k) s + a =
                    2 EXP (64 * val k) *
                    (2 EXP (64 * val k) * val(C_RETURN s) +
                    bignum_from_memory
                      (word_add z (word(8 * val k)),val k) s)))
          (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [Q8; Q9; Q10; Q11; Q12; Q13; Q14; Q15] ,,
            MAYCHANGE [X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30] ,,
            MAYCHANGE [memory :> bytes(z,8 * 2 * val k);
                      memory :> bytes(word_sub stackpointer (word 128),128);
                      memory :> bytes(m_sub_precalc,8 * 12 * (val k DIV 4 - 1))])`;;


e(W64_GEN_TAC `k:num` THEN
  MAP_EVERY X_GEN_TAC [`z:int64`; `m:int64`] THEN
  W64_GEN_TAC `w:num` THEN
  MAP_EVERY X_GEN_TAC [`m_precalc:int64`; `a:num`; `n:num`; `pc:num`; `stackpointer:int64`] THEN
  REWRITE_TAC[BIGNUM_EMONTREDC_8N_NEON_EXEC; ALL; ALLPAIRS; NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  BIGNUM_TERMRANGE_TAC `2 * k` `a:num` THEN
  BIGNUM_TERMRANGE_TAC `k:num` `n:num` THEN
  ENSURES_EXISTING_PRESERVED_TAC `SP` THEN
  ABBREV_TAC `k4 = k DIV 4` THEN
  COMMENT_TAC "Intro");;

  (*** Degenerate k/4 = 0 case ***)

e(ASM_CASES_TAC `k4 = 0` THENL
   [UNDISCH_THEN `k4 = 0` SUBST_ALL_TAC THEN
    
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ENSURES_INIT_TAC "s0" THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--6) THEN
    UNDISCH_TAC `read PC s6 =
      (if val (word_ushr (word k:(64)word) 2) < 1 then word (pc + 2192) else word (pc + 84))` THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`; ARITH_RULE `0 < 1`] THEN
    DISCH_TAC THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (7--8) THEN
    ENSURES_FINAL_STATE_TAC THEN
    UNDISCH_TAC `8 divides k` THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`;
                    DIVIDES_DIV_MULT; MULT_CLAUSES; ARITH_RULE `0 < 1`;
                    DIV_0; ARITH_RULE `k DIV 8 = k DIV 4 DIV 2`;
                    WORD_RULE `word_add (word_sub x y) y:(64)word = x`] THEN
    ASM_CASES_TAC `k = 0` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "a" THEN REWRITE_TAC[ASSUME `k = 0`] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES; VAL_WORD_0] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
    CONV_TAC WORD_RULE;
    ALL_TAC] THEN
  COMMENT_TAC "k=0 done");;

  (*** Restate things in terms of k' = k * k DIV 4 for naturalness ***)

e(ABBREV_TAC `k' = 4 * k4` THEN
  ABBREV_TAC `a' = lowdigits a (2 * k')` THEN
  ABBREV_TAC `n' = lowdigits n k'` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x54`
   `\s. read X12 s = word(k4 - 1) /\
        read X26 s = word k4 /\
        read X1 s = z /\
        read X2 s = m /\
        read X3 s = word w /\
        read X4 s = m_precalc /\
        read SP s = word_sub stackpointer (word 128) /\
        aligned 16 stackpointer /\
        bignum_from_memory (z,2 * k') s = a' /\
        bignum_from_memory (m,k') s = n'` THEN
  CONJ_TAC THENL
   [ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--6) THEN
    ASM_REWRITE_TAC[VAL_WORD_USHR; NUM_REDUCE_CONV `2 EXP 2`] THEN
    ASM_REWRITE_TAC[ARITH_RULE `n < 1 <=> n = 0`] THEN
    ASM_REWRITE_TAC[WORD_SUB; ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    REWRITE_TAC[WORD_RULE `word_sub x z = word_sub y z <=> x = y`] THEN
    ASM_REWRITE_TAC[word_ushr; NUM_REDUCE_CONV `2 EXP 2`] THEN
    CONJ_TAC THENL [CONV_TAC WORD_RULE; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["a'"; "n'"; "a"; "n"] THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    MAP_EVERY EXPAND_TAC ["k'"; "k4"] THEN
    CONJ_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC;
    ALL_TAC] THEN
  COMMENT_TAC "after first branch");;


(* TODO: NO CHEAT_TAC HERE! *)
e(SUBGOAL_THEN `k4 > 1` ASSUME_TAC THENL [CHEAT_TAC; ALL_TAC]);;

e(ENSURES_SEQUENCE_TAC `pc + 0xe0`
   `\s. read X12 s = word(k4 - 1) /\
        read X26 s = word k4 /\
        read X1 s = z /\
        read X2 s = m /\
        read X3 s = word w /\
        read X30 s = m_precalc /\
        read SP s = word_sub stackpointer (word 128) /\
        aligned 16 stackpointer /\
        bignum_from_memory (z,2 * k') s = a' /\
        bignum_from_memory (m,k') s = n' /\
        bignum_from_memory (m_precalc,12*(k4-1)) s = m_precalc_value n' (k4-1)` THEN
  CONJ_TAC THENL [

  ENSURES_WHILE_PDOWN_TAC `k4 - 1` `pc + 0x64` `pc + 0xd4`
      `\i s. // Preservation of original data
             (read X12 s = word(k4 - 1) /\
              read X26 s = word k4 /\
              read X1 s = z /\
              read X25 s = m /\
              read X3 s = word w /\
              read X24 s = m_precalc /\
              read SP s = word_sub stackpointer (word 128) /\
              aligned 16 stackpointer /\
              bignum_from_memory (z,2 * k') s = a' /\
              bignum_from_memory (m,k') s = n' /\
              // Loop-dependent data
              read X27 s = word i /\
              read X30 s = word_add m_precalc (word (8 * 12 * (k4 - 1 - i))) /\
              read X2 s = word_add m (word (8 * 4 * (k4 - 1 - i))) /\
              bignum_from_memory (m_precalc,12*(k4-1-i)) s = m_precalc_value n' (k4-1-i)) /\
             (read ZF s <=> i = 0)` THEN REPEAT CONJ_TAC THENL [
    (* 1. k4 - 1 > 0 *)
    ASM_ARITH_TAC;

    (* 2. To loop start *)
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--4) THEN
    REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN
    CHECK_NUM_GOALS 1 "Single goal (... = m_precalc_value) must remain" THEN
    REWRITE_TAC[m_precalc_value;ARITH_RULE`8*12*0=0`;READ_MEMORY_BYTES_0] THEN
    FAIL_TAC "fail0";

    (* 3. Loop body *)
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    (* Two ldps *)
    SUBGOAL_THEN
       `read (memory :> bytes64
            (word_add m (word (8 * 4 * (k4 - 1 - (i + 1)) + 32)))) s0 =
          word (bigdigit n' (4 * (k4 - 1 - (i + 1)) + 4)) /\
        read (memory :> bytes64
            (word_add m (word (8 * 4 * (k4 - 1 - (i + 1)) + 40)))) s0 =
          word (bigdigit n' (4 * (k4 - 1 - (i + 1)) + 5)) /\
        read (memory :> bytes64
            (word_add m (word (8 * 4 * (k4 - 1 - (i + 1)) + 48)))) s0 =
          word (bigdigit n' (4 * (k4 - 1 - (i + 1)) + 6)) /\
        read (memory :> bytes64
            (word_add (word_add m (word (8 * 4 * (k4 - 1 - (i + 1))))) (word 56))) s0 =
          word (bigdigit n' (4 * (k4 - 1 - (i + 1)) + 7))`
      (LABEL_TAC "H_a0_to_a3") THENL [
      GEN_REWRITE_TAC (DEPTH_BINOP_CONV `(/\):bool->bool->bool`) [GSYM VAL_EQ] THEN
      REWRITE_TAC[VAL_WORD_BIGDIGIT] THEN
      EXPAND_TAC "n'" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      IMP_REWRITE_TAC[TAUT `c = T ==> (if c then x else y) = x`] THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      IMP_REWRITE_TAC[WORD_RULE
        `i0=j0 ==> val (read (memory :> bytes64 (word_add m (word i0))) s0) =
                  val (read (memory :> bytes64 (word_add m (word j0))) s0)`] THEN
      REPEAT CONJ_TAC THEN ASM_ARITH_TAC;

      ALL_TAC
    ] THEN
    COMMENT_TAC "Proved H_a0_to_a3" THEN
    ASSERT_USING_UNDISCH_AND_ARITH_TAC
        `(8 * 12 * (k4 - 1 - (i + 1)) + 8) + 8 <= 18446744073709551616`
        `8 * 12 * (k4 - 1) < 2 EXP 64` THEN
    ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--28) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL [
      CONV_TAC WORD_RULE;

      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN AP_TERM_TAC THEN AP_TERM_TAC
        THEN UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;

      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN AP_TERM_TAC THEN AP_TERM_TAC
        THEN UNDISCH_TAC `i < k4 - 1` THEN ARITH_TAC;

      ASSERT_USING_UNDISCH_AND_ARITH_TAC `k4 - 1 - i = (k4 - 1 - (i + 1)) + 1` `i < k4 - 1` THEN
      REWRITE_TAC[ASSUME `k4 - 1 - i = k4 - 1 - (i + 1) + 1`] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
      RULE_ASSUM_TAC (REWRITE_RULE [GSYM BIGNUM_FROM_MEMORY_BYTES]) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ARITH_RULE`12 * 1 = (((((((((((0+1)+1)+1)+1)+1)+1)+1)+1)+1)+1)+1)+1`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP; BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      CONV_TAC (DEPTH_CONV NUM_ADD_CONV) THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
      ASM_REWRITE_TAC[ARITH_RULE `x+0=x`] THEN
      REWRITE_TAC[m_precalc_value] THEN
      CONV_TAC (ONCE_DEPTH_CONV NUM_MULT_CONV) THEN
      IMP_REWRITE_TAC[ARITH_RULE`x=y ==> x+z=z+y`] THEN
      REWRITE_TAC[EQ_MULT_LCANCEL] THEN DISJ2_TAC THEN
      REWRITE_TAC[ARITH_RULE`2 EXP 0 = 1`;MULT_CLAUSES;ADD_CLAUSES;ADD_ASSOC] THEN
      REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;ARITH_RULE`1*4=4`] THEN
      REWRITE_TAC[GSYM ADD_ASSOC] THEN
      CONV_TAC (DEPTH_CONV NUM_ADD_CONV) THEN
      REWRITE_TAC[ARITH_RULE`(k4 - 1 - (i + 1)) * 4 = 4 * (k4 - 1 - (i + 1))`;VAL_WORD_BIGDIGIT] THEN
      FAIL_TAC "fail1";

      REWRITE_TAC[WORD_SUB_ADD] THEN
      MATCH_MP_TAC VAL_WORD_EQ_ZERO THEN
      MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `i < k4 - 1`] THEN
      EXPAND_TAC "k4" THEN
      ARITH_TAC
    ];

    (* 4. Backedge *)
    REPEAT STRIP_TAC THEN ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [1] THEN
    MATCH_MP_TAC (TAUT `a ==> ((if a then b else c) = b)`) THEN
    IMP_REWRITE_TAC[VAL_WORD_EQ] THEN
    REWRITE_TAC[DIMINDEX_64] THEN
    MAP_EVERY UNDISCH_TAC [`k < 2 EXP 64`; `i < k4 - 1`] THEN EXPAND_TAC "k4" THEN ARITH_TAC;

    (* 5. Loop termination to 0xe0 *)
    ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--3) THEN
    RULE_ASSUM_TAC (REWRITE_RULE [SUB_0]) THEN
    ASM_REWRITE_TAC[] THEN FAIL_TAC "term to 0xe0"
  ];
  
  ALL_TAC
]);;

(* 0xe0 to 0x898 *)
e(COMMENT_TAC "starting outer loop");;

(* Let's replace k with k', because k' = 4 * k4 which
   explicitly says it is a multiple of 4. *)
e(SUBGOAL_THEN `k = k':num` SUBST_ALL_TAC THENL [
  EXPAND_TAC "k'" THEN
  EXPAND_TAC "k4" THEN
  REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
  MATCH_MP_TAC DIVIDES_LMUL2 THEN
  EXISTS_TAC `2` THEN
  ASM_REWRITE_TAC[ARITH_RULE`2*4=8`];

  ALL_TAC]);;
(* Also replace n with n', and rename n' to n. *)
e(SUBGOAL_THEN `n = n':num` SUBST_ALL_TAC THENL [
  EXPAND_TAC "n'" THEN MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC LOWDIGITS_SELF
  THEN ASM_REWRITE_TAC[]; ALL_TAC]);;
(* Same for a and a'. *)
e(SUBGOAL_THEN `a = a':num` SUBST_ALL_TAC THENL [
  EXPAND_TAC "a'" THEN MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC LOWDIGITS_SELF
  THEN ASM_REWRITE_TAC[]; ALL_TAC]);;

(* Now restrict the scope to bignum_emontredc_8n_neon_outerloop: 0xf4 ~ 0x888 *)
(* TODO: update this loop invariant *)
e(ENSURES_WHILE_PDOWN_TAC `k4:num` `pc + 0xf4` `pc + 0x888`
    `\i s. (read X0 s = word(32 * (k4 - 1)) /\
            read X1 s = word_add z (word(8 * 4 * (k4-i))) /\
            read X2 s = m /\
            read X30 s = m_precalc /\
            read SP s = word_sub stackpointer (word 128) /\
            aligned 16 stackpointer /\
            read Q29 s = word_join (word 4294967295:int64) (word 4294967295:int64) /\
            // Buffers
            bignum_from_memory
                (word_add z (word(8 * (k' + 4 * (k4-i)))),
                 2 * k' - (k' + 4 * (k4-i))) s =
              highdigits a' (k' + 4 * (k4-i)) /\
            bignum_from_memory (m,k') s = n' /\
            ((n' * w + 1 == 0) (mod (2 EXP 64))
              ==> 2 EXP (64 * 4 * (k4-i)) *
                (2 EXP (64 * k') * val(word_neg(read X28 s)) +
                 bignum_from_memory (word_add z (word(8 * 4 * (k4-i))),k') s) =
               bignum_from_memory(z,4 * (k4-i)) s * n' +
                 lowdigits a' (k' + 4 * (k4-i))) /\
            bignum_from_memory (m_precalc,12*(k4-1)) s = m_precalc_value n' (k4-1) /\
            // Stack
            read (memory :> bytes64 (word_sub stackpointer (word 128))) s = word w /\
            read (memory :> bytes64 (word_sub stackpointer (word 120))) s = m_precalc /\
            read (memory :> bytes64 (word_sub stackpointer (word 112))) s = word i
          ) /\ (read ZF s <=> i = 0)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [

  (* to loop header *)
  ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--5) THEN
  CONV_TAC (DEPTH_CONV NUM_MULT_CONV) THEN
  REWRITE_TAC[WORD_ADD_0; ADD_CLAUSES; ARITH_RULE`2*k-k=k`;READ_MEMORY_BYTES_0] THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THEN TRY (CONV_TAC WORD_BLAST) THENL [
    EXPAND_TAC "a'" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY;ARITH_RULE`2*k-k=k`];

    REWRITE_TAC[ARITH_RULE`2 EXP 0=1`;WORD_RULE`word_neg (word 0:int64)=word 0`] THEN
    REWRITE_TAC[VAL_WORD_0;MULT_CLAUSES] THEN
    EXPAND_TAC "a'" THEN
    REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;LOWDIGITS_BIGNUM_FROM_MEMORY;ARITH_RULE`MIN (2*k') k'=k'`];

    REWRITE_TAC[WORD_RULE `word_sub t (word 120):int64 =
        word_add (word_sub t (word 128)) (word 8)`] THEN
    ASM_REWRITE_TAC[];

    REWRITE_TAC[WORD_RULE `word_sub t (word 112):int64 =
        word_add (word_sub t (word 128)) (word 16)`] THEN
    ASM_REWRITE_TAC[]
  ] THEN NO_TAC;

  (* 2. loop body *)
  ALL_TAC;

  (* 3. backedge *)
  REPEAT STRIP_TAC THEN
  ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [1];

  (* 4. backedge untaken and go to the end *)
  REWRITE_TAC[SUB_0;BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  ABBREV_TAC `sign = read X28 s0` THEN
  ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--4) THEN
  SUBST_ALL_TAC (ASSUME `4 * k4 = k'`) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; CONV_TAC WORD_RULE] THEN
  DISCH_THEN (fun thm -> FIRST_X_ASSUM (fun athm -> MP_TAC (MP athm thm))) THEN
  ASM_REWRITE_TAC[ARITH_RULE`k'+k'=2*k'`;word_neg] THEN
  ARITH_TAC
]);;
e(COMMENT_TAC "before starting outer loop's body - 4 blocks of multiplications");;

e(REPEAT STRIP_TAC);;
(* Before diving, clean up expressions a bit *)
e(GHOST_INTRO_TAC `cout:num` `\s. val (word_neg (read X28 s))`);;
e(ABBREV_TAC `j = k4 - (i+1)`);;
e(SUBGOAL_THEN `k4 - i = j + 1` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]);;
e(SUBGOAL_THEN `(i=0) <=> (j=k4-1)` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]);;
e(SUBGOAL_THEN `j < k4` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC]);;
e(SUBGOAL_THEN `i = k4 - j - 1` (fun th -> REWRITE_TAC[th]) THENL
  [ASM_ARITH_TAC; ALL_TAC]);;
e(REMOVE_ASSUMS_INCLUDING `i:num`);;

e(ABBREV_TAC `zj = word_add z (word (8 * 4 * j)):int64`);;
e(SUBGOAL_THEN
  `word_add z (word (8 * 4 * (j+1))):int64 = word_add zj (word 32)` SUBST_ALL_TAC THENL [
  EXPAND_TAC "zj" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
  ALL_TAC]);;
e(SUBGOAL_THEN
  `word_add z (word (8 * (k' + 4 * j))):int64 =
   word_add zj (word (8 * k'))` SUBST_ALL_TAC THENL [
  EXPAND_TAC "zj" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
  ALL_TAC]);;
e(SUBGOAL_THEN
  `2 * k' - (k' + 4 * j) = k' - 4 * j` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC]);;
e(SUBGOAL_THEN
  `word_add z (word (8 * (k' + 4 * (j+1)))):int64 =
   word_add zj (word (8 * k' + 32))` SUBST_ALL_TAC THENL [
  EXPAND_TAC "zj" THEN REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
  ALL_TAC]);;
e(SUBGOAL_THEN
  `2 * k' - (k' + 4 * (j+1)) = k' - 4 * (j+1)` SUBST_ALL_TAC
  THENL [ASM_ARITH_TAC; ALL_TAC]);;
e(COMMENT_TAC "abbreviated");;

e(SUBGOAL_THEN `!s. bignum_from_memory (zj,k') s = lowdigits (bignum_from_memory (zj,k'+4) s) k'`
  (fun th -> REWRITE_TAC[th]) THENL [
  REWRITE_TAC[LOWDIGITS_BIGNUM_FROM_MEMORY] THEN REWRITE_TAC[ARITH_RULE`MIN (k'+4) k'=k'`];
  ALL_TAC
  ]);;
e(SUBGOAL_THEN
   `!s. bignum_from_memory (z,4 * (j + 1)) s =
        2 EXP (64 * 4 * j) * bignum_from_memory(zj,4) s +
        bignum_from_memory(z,4 * j) s`
   (fun th -> REWRITE_TAC[th])
  THENL
   [REWRITE_TAC[ARITH_RULE `4 * (j + 1) = 4 * j + 4`] THEN
    ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT];
    ALL_TAC]);;
e(SUBGOAL_THEN
   `!s. bignum_from_memory (word_add zj (word (8 * k')),k' - 4 * j) s =
        highdigits a' (k' + 4 * j) <=>
        highdigits (bignum_from_memory(zj,k'+4) s) k' =
        lowdigits (highdigits a' (k' + 4 * j)) 4 /\
        bignum_from_memory
         (word_add zj (word (8 * k' + 32)),k' - 4 * (j + 1)) s =
        highdigits a' (k' + 4 * (j + 1))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN
    REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ADD_SUB2] THEN
    SUBGOAL_THEN
     `k' - 4 * j = 4 + (k' - 4 * (j + 1))`
    SUBST1_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_SPLIT] THEN
    MP_TAC(SPECL [`highdigits a' (k' + 4 * j)`; `4`]
     (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM th]) THEN
    SIMP_TAC[LEXICOGRAPHIC_EQ; BIGNUM_FROM_MEMORY_BOUND; LOWDIGITS_BOUND] THEN
    REWRITE_TAC[HIGHDIGITS_HIGHDIGITS] THEN
    REWRITE_TAC[ARITH_RULE `(k' + 4 * j) + 4 = k' + 4 * (j + 1)`] THEN
    REWRITE_TAC[WORD_RULE
     `word_add (word_add zj (word (8 * k))) (word (8 * 4)) =
      word_add zj (word (8 * k + 32))`] THEN
    MATCH_ACCEPT_TAC CONJ_SYM;
    ALL_TAC]);;

e(GHOST_INTRO_TAC `z1:num` `bignum_from_memory(zj,k'+4)`);;
e(BIGNUM_TERMRANGE_TAC `k' + 4` `z1:num`);;
e(GHOST_INTRO_TAC `q1:num` `bignum_from_memory(z,4 * j)`);;
e(BIGNUM_TERMRANGE_TAC `4 * j` `q1:num`);;
e(GLOBALIZE_PRECONDITION_TAC);;

e(COMMENT_TAC "Renaming 'stackpointer - 128' to make NONOVERLAPPING_TAC happy");;
e(ABBREV_TAC `sp = word_sub stackpointer (word 128):int64`);;
e(SUBGOAL_THEN `aligned 16 (sp:int64)` ASSUME_TAC THENL [
  EXPAND_TAC "sp" THEN MATCH_MP_TAC ALIGNED_WORD_SUB THEN
  ASM_REWRITE_TAC[aligned] THEN
  REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN CONV_TAC NUM_DIVIDES_CONV;
  ALL_TAC]);;
e(SUBGOAL_THEN `word_sub stackpointer (word 120) = word_add sp (word 8):int64` (fun th -> REWRITE_TAC[th]) THENL [
  EXPAND_TAC "sp" THEN CONV_TAC WORD_RULE; ALL_TAC]);;
e(SUBGOAL_THEN `word_sub stackpointer (word 112) = word_add sp (word 16):int64` (fun th -> REWRITE_TAC[th]) THENL [
  EXPAND_TAC "sp" THEN CONV_TAC WORD_RULE; ALL_TAC]);;
e(REMOVE_ASSUMS_INCLUDING `stackpointer:int64`);;
e(COMMENT_TAC "nonoverlapping between storing to sp and other addrs");;
e(SUBGOAL_THEN
    `nonoverlapping (zj:int64,8*k'+32+8*(k'-4*(j+1))) (sp:int64,128) /\
     nonoverlapping (z,8*4*j) (sp:int64,128)`
    MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL [
  EXPAND_TAC "zj" THEN REPEAT CONJ_TAC THEN TRY NONOVERLAPPING_TAC THEN
  REWRITE_TAC[WORD_ADD_ASSOC_CONSTS] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [`val (z:int64)`;
      `8*k'+32+8*(k'-4*(j+1))`; `val (sp:int64)`; `128`] THEN
  ASM_REWRITE_TAC[CONTAINED_MODULO_REFL; LE_REFL] THEN
  REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;ADD_MOD_MOD_REFL] THEN
  REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
  MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN ASM_ARITH_TAC;

  STRIP_TAC]);;

e(COMMENT_TAC "stripping the last increment of x26 at the end of the loop");;
e(ENSURES_SEQUENCE_TAC `pc + 0x878`
  `\s. read X0 s = word (32 * (k4 - 1)) /\
       read X1 s = word_add zj (word (32 * (k4 - 1))) /\
       read X2 s = m /\
       read X30 s = m_precalc /\
       read SP s = sp /\
       read Q29 s = word_join (word 4294967295:int64) (word 4294967295:int64) /\
       bignum_from_memory (word_add zj (word (8 * k' + 32)),k' - 4 * (j + 1))
       s =
       highdigits a' (k' + 4 * (j + 1)) /\
       bignum_from_memory (m,k') s = n' /\
       ((n' * w + 1 == 0) (mod (2 EXP 64))
        ==> 2 EXP (64 * 4 * (j + 1)) *
            (2 EXP (64 * k') * val (word_neg (read X28 s)) +
             bignum_from_memory (word_add zj (word 32),k') s) =
            (2 EXP (64 * 4 * j) * bignum_from_memory (zj,4) s +
             bignum_from_memory (z,4 * j) s) *
            n' +
            lowdigits a' (k' + 4 * (j + 1))) /\
       bignum_from_memory (m_precalc,12 * (k4 - 1)) s =
       m_precalc_value n' (k4 - 1) /\
       read (memory :> bytes64 sp) s = word w /\
       read (memory :> bytes64 (word_add sp (word 8))) s =
       m_precalc /\
       read (memory :> bytes64 (word_add sp (word 16))) s = word (k4 - j) /\
       read X26 s = word (k4 - j)` THEN REPEAT CONJ_TAC THENL [
  ALL_TAC;

  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
  ENSURES_INIT_TAC "s0" THEN
  ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--2) THEN
  DISCARD_MATCHING_ASSUMPTIONS [`word_add z (word (8 * 4 * j)) = zj:int64`] THEN
  ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (3--4) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY (CONV_TAC WORD_RULE) THENL [
    UNDISCH_TAC `j < k4` THEN
    (* `j < k4 ==> word_sub (word (k4 - j)) (word 1) = word (k4 - j - 1)` *)
    CHEAT_TAC;

    UNDISCH_TAC `j < k4` THEN
    (* `j < k4 ==> (val (word_sub (word (k4 - j)) (word 1)) = 0 <=> j = k4 - 1`) *)
    CHEAT_TAC
  ]
]);;

e(COMMENT_TAC "Truly starting the outer loop ");;
(* starting from 244 (0xf4) *)

(* [nonoverlapping_modulo (2 EXP 64) (val zj,8 * k' + 32 + 8 * (k' - 4 * (j + 1)))
(val m_precalc,8 * 12 * (k4 - 1))] <-- new
[nonoverlapping_modulo (2 EXP 64) (val m,8 * k') (val zj,8 * k' + 32 + 8 * (k' - 4 * (j + 1)))] <-- new
*)
e(SUBGOAL_THEN
   `nonoverlapping (zj:int64, 8 * k' + 32 + 8 * (k' - 4 * (j + 1)))
                   (m_precalc:int64, 8 * 12 * (k4 - 1)) /\
    nonoverlapping (m:int64, 8*k') (zj, 8 * k' + 32 + 8 * (k' - 4 * (j + 1)))`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL [
  EXPAND_TAC "zj" THEN CONJ_TAC THEN TRY NONOVERLAPPING_TAC;

  REPEAT STRIP_TAC]);;

e(SUBGOAL_THEN
    `nonoverlapping (word pc:int64,LENGTH bignum_emontredc_8n_neon_mc)
                    (zj:int64,8*k'+32+8*(k'-4*(j+1)))`
    MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES;BIGNUM_EMONTREDC_8N_NEON_EXEC]
  THENL [
  REWRITE_TAC[GSYM (ASSUME `word_add z (word (8 * 4 * j)):int64 = zj`)] THEN
  MATCH_MP_TAC NONOVERLAPPING_MODULO_SUBREGIONS THEN
  MAP_EVERY EXISTS_TAC [
      `pc:num`; `LENGTH bignum_emontredc_8n_neon_mc`;
      `val (z:int64)`; `8*2*k'`] THEN
  REWRITE_TAC[VAL_WORD_ADD;VAL_WORD;DIMINDEX_64;ADD_MOD_MOD_REFL] THEN
  ASM_REWRITE_TAC[BIGNUM_EMONTREDC_8N_NEON_EXEC;CONTAINED_MODULO_REFL] THEN
  REWRITE_TAC[LE_REFL] THEN
  REWRITE_TAC[CONTAINED_MODULO_LMOD] THEN
  MATCH_MP_TAC CONTAINED_MODULO_OFFSET_SIMPLE THEN
    MAP_EVERY UNDISCH_TAC [`j < k4`; `4 * k4 = k'`] THEN
  ARITH_TAC;

  STRIP_TAC]);;

e(SUBGOAL_THEN
   `nonoverlapping (zj:int64, 8 * k' + 32 + 8 * (k' - 4 * (j + 1)))
                   (z:int64, 8 * 4 * j)`
  MP_TAC THEN REWRITE_TAC[NONOVERLAPPING_CLAUSES] THENL [
  REWRITE_TAC[GSYM (ASSUME `word_add z (word (8 * 4 * j)):int64 = zj`)] THEN
    NONOVERLAPPING_TAC;
  REPEAT STRIP_TAC]);;

e(REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES]);;
e(ENSURES_INIT_TAC "s0");;

(* Prepare 4 loads at zj *)
e(SUBGOAL_THEN
  `!i. i < 4 ==> bigdigit (bignum_from_memory (zj,k'+4) s0) i = bigdigit z1 i`
  MP_TAC THENL [
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN NO_TAC;
  ALL_TAC] THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV)) THEN
  REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
  REWRITE_TAC[ARITH_RULE `0<k'+4/\1<k'+4/\2<k'+4/\3<k'+4`] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  STRIP_TAC);;

(* Prepare 8 loads at m *)
e(SUBGOAL_THEN
  `!i. i < 8 ==> bigdigit (bignum_from_memory (m,k') s0) i = bigdigit n' i`
  MP_TAC THENL [
  ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN NO_TAC;
  ALL_TAC] THEN
  CONV_TAC(LAND_CONV(EXPAND_CASES_CONV)) THEN
  REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
  SUBGOAL_THEN `0<k'/\1<k'/\2<k'/\3<k'/\4<k'/\5<k'/\6<k'/\7<k'` (fun t->REWRITE_TAC[t]) THENL
  [ASM_ARITH_TAC;ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [VAL_WORD_GALOIS; DIMINDEX_64; BIGDIGIT_BOUND] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_MULT_CONV)) THEN
  REWRITE_TAC[WORD_ADD_0] THEN
  STRIP_TAC);;

e(ASSERT_READ_BYTES128_EQ_JOIN64_TAC `word_add m (word 16):int64` "s0");;

e(SUBGOAL_THEN `read (memory :> bytes (word_add zj (word 32), 8*k')) s0 =
    highdigits z1 4` ASSUME_TAC THENL [
  EXPAND_TAC "z1" THEN REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES] THEN
  REWRITE_TAC[HIGHDIGITS_BIGNUM_FROM_MEMORY; ARITH_RULE`8*4=32`; ARITH_RULE`(k'+4)-4=k'`];
  ALL_TAC]);;

e(ASSERT_READ_BYTES128_EQ_JOIN64_TAC `word_add m (word 32):int64` "s0");;

e(ASSERT_READ_BYTES128_EQ_JOIN64_TAC `word_add m (word 48):int64` "s0");;

(*
(* [read (memory :> bytes (m_precalc,8 * 12 * (k4 - 1))) s73 =
m_precalc_value n' (k4 - 1)] *)
*)
e(SUBGOAL_THEN
    `!i. i < 6 ==> bigdigit (bignum_from_memory (m_precalc, 12*(k4-1)) s0) i  =
                   bigdigit (m_precalc_value n' (k4-1)) i`
    MP_TAC THENL [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN NO_TAC;ALL_TAC] THEN
  CONV_TAC (LAND_CONV EXPAND_CASES_CONV) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
  REPEAT_I_N 0 6
  (fun i -> let g = subst [(mk_numeral(Int i),`__i__:num`)] `__i__ < 12 * (k4-1)` in
    SUBGOAL_THEN g (fun thm -> REWRITE_TAC[thm]) THENL [
      UNDISCH_TAC `k4>1` THEN ARITH_TAC; ALL_TAC]) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM VAL_WORD_BIGDIGIT] THEN
  CONV_TAC ((LAND_CONV o ONCE_DEPTH_CONV) (NUM_REDUCE_CONV)) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [VAL_EQ;WORD_ADD_0] THEN
  REPEAT STRIP_TAC);;

time e(ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (1--47));; (* stp x11, x25, [x1] *)
e(ASSERT_READ_BYTES128_EQ_JOIN64_TAC `zj:int64` "s47");;(* This cannot be hoisted. *)
time e(ARM_STEPS_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC (48--131));; 
  (* 50: ldr q16, [x1] *)
  (* 62: stp x17, x26, [sp, #32] *)
  (* 73: ldp x23, x14, [x2, #16] *)
  (* 77: ldp x8, x24, [x30, #16] *)
  (* 79: ldr q9, [x2, #32]! *)
  (* 82: ldr q13, [x2, #16] *)
  (* 123: stp x20, x26, [sp, #48] *)
  (* 131: stp	x9, x26, [sp, #80] *)

(* val (read (memory :> bytes64 (word_add m_precalc (word (8 * 0)))) s73) =
 bigdigit (m_precalc_value n' (k4 - 1)) 0 /\
 val (read (memory :> bytes64 (word_add m_precalc (word (8 * 1)))) s73) =
 bigdigit (m_precalc_value n' (k4 - 1)) 1 /\
 val (read (memory :> bytes64 (word_add m_precalc (word (8 * 2)))) s73) =
 bigdigit (m_precalc_value n' (k4 - 1)) 2 /\
 val (read (memory :> bytes64 (word_add m_precalc (word (8 * 3)))) s73) =
 bigdigit (m_precalc_value n' (k4 - 1)) 3 /\
 val (read (memory :> bytes64 (word_add m_precalc (word (8 * 4)))) s73) =
 bigdigit (m_precalc_value n' (k4 - 1)) 4 /\
 val (read (memory :> bytes64 (word_add m_precalc (word (8 * 5)))) s73) =
 bigdigit (m_precalc_value n' (k4 - 1)) 5 *)
(*
e(ENSURES_SEQUENCE_TAC `pc + 0x888`
   `\s. (read X0 s = word (32 * (k4 - 1)) /\
        read X1 s = word_add zj (word 32) /\
        read X2 s = m /\
        read X30 s = m_precalc /\
        read SP s = word_sub stackpointer (word 128) /\
        read Q29 s = word_join (word 4294967295:int64) (word 4294967295:int64) /\
        bignum_from_memory (word_add zj (word (8 * k' + 32)),k' - 4 * (j + 1))
        s =
        highdigits a' (k' + 4 * (j + 1)) /\
        bignum_from_memory (m,k') s = n' /\
        bignum_from_memory (m_precalc,12 * (k4 - 1)) s =
        m_precalc_value n' (k4 - 1) /\
        read (memory :> bytes64 (word_sub stackpointer (word 128))) s = word w /\
        read (memory :> bytes64 (word_sub stackpointer (word 120))) s =
        m_precalc /\
        read (memory :> bytes64 (word_sub stackpointer (word 112))) s =
        word k4 /\
        (read ZF s <=> j = k4 - 1) /\
        bignum_from_memory (z,4 * j) s = q1 /\
        ((n' * w + 1 == 0) (mod (2 EXP 64))
          ==> 2 EXP (64 * 4) *
              (2 EXP (64 * k') * val (word_neg (read X28 s)) +
              bignum_from_memory (word_add zj (word 32),k') s) =
              bignum_from_memory(zj,4) s * n' + 2 EXP (64 * k') * cout + z1))`
    THEN CONJ_TAC THENL [
  ALL_TAC;

  ARM_SIM_TAC BIGNUM_EMONTREDC_8N_NEON_EXEC [] THEN
  DISCH_THEN(fun th ->
     REPEAT(FIRST_X_ASSUM(ASSUME_TAC o C MATCH_MP th))) THEN
  REWRITE_TAC[EXP_ADD; ARITH_RULE
     `64 * 4 * (i + 1) = 64 * 4 * i + 64 * 4`] THEN
  ASM_REWRITE_TAC[GSYM MULT_ASSOC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; EQ_ADD_LCANCEL] THEN
  MP_TAC(SPECL [`z1:num`; `k':num`] (CONJUNCT1 HIGH_LOW_DIGITS)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[ARITH_RULE
    `ee * e * c + ee * (e * h + l):num =
    (ee * (e * c + l)) + (ee * e) * h`] THEN
  REWRITE_TAC[GSYM EXP_ADD; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
  REWRITE_TAC[lowdigits; highdigits; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN
  REWRITE_TAC[ARITH_RULE `64 * 4 * j + 64 * k' = 64 * k' + 64 * 4 * j`] THEN
  SPEC_TAC(`64 * k' + 64 * 4 * j`,`j':num`) THEN
  REWRITE_TAC[EXP_ADD; MOD_MULT_MOD] THEN ARITH_TAC]);;

e(SUBGOAL_THEN `(n' * w + 1 == 0) (mod (2 EXP 64)) ==> cout < 2`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `2 EXP (64 * 4 * j) * (2 EXP (64 * k') * cout + lowdigits z1 k') <
      2 EXP (64 * 4 * j) * 2 EXP (64 * k') * 2`
    MP_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC (ARITH_RULE
       `x < d * e /\ y < e * d ==> x + y < d * e * 2`) THEN
      ASM_SIMP_TAC[LT_MULT2] THEN REWRITE_TAC[GSYM EXP_ADD] THEN
      REWRITE_TAC[LOWDIGITS_BOUND; GSYM LEFT_ADD_DISTRIB];
      DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
       `d * (e * c + l):num < x ==> d * e * c < x`)) THEN
      REWRITE_TAC[LT_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]];
    ALL_TAC]);;

(* z1 = bignum read of buffer z from zj to zj + 8*(k'+4),
        which is z+8j to z+8j + 8*(k'+4)
        (word width: k'+4)
        Note that after initial Montgomery 4-block, first 4 words
        will change. *)
(* a' = initial buffer z input (word width: 2k') *)
(* q1 = bignum read of buffer z to z + 4j (word width: j) *)
(* n' = prime *)
(* After this point, z1 in this proof = a in scalar proof *)

(*** The initial Montgomery 4-block ***)
(*
e(ENSURES_SEQUENCE_TAC `pc + 0x444`
   `\s. read X0 s = word (32 * (k4 - 1)) /\
        read X1 s = zj /\
        read X2 s = m /\
        read X30 s = m_precalc /\
        read SP s = word_sub stackpointer (word 128) /\
        read Q29 s = word_join (word 4294967295) (word 4294967295) /\
        bignum_from_memory (m,k') s = n' /\
        bignum_from_memory (m_precalc,12 * (k4 - 1)) s =
            m_precalc_value n' (k4 - 1) /\
        read (memory :> bytes64 (word_sub stackpointer (word 128))) s = word w /\
        read (memory :> bytes64 (word_sub stackpointer (word 120))) s =
            m_precalc /\
        read (memory :> bytes64 (word_sub stackpointer (word 112))) s = word k4 /\
        val (word_neg (read X28 s)) = cout /\
        // Iteration-specific invariants
        bignum_from_memory (z,4 * j) s = q1 /\
        bignum_from_memory (zj,k' + 4) s = z1 /\
        ((n' * w + 1 == 0) (mod (2 EXP 64))
         ==> 2 EXP (64 * 4) *
             bignum_of_wordlist
              [read X12 s; read X13 s; read X14 s; read X15 s] =
             bignum_from_memory(zj,4) s * lowdigits n' 4 + lowdigits z1 4) /\
        bignum_from_memory (word_sub stackpointer (word 96), 96) s =
            z_precalc_value (bignum_from_memory (zj,4) s)`);;*)
*)