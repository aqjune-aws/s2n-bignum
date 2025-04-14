(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying (with truncation or extension) bignums                            *)
(*                                                                           *)
(* Input x[n]; output z[k]                                                   *)
(*    extern void bignum_copy                                                *)
(*      (uint64_t k, uint64_t *z, uint64_t n, uint64_t *x);                  *)
(*                                                                           *)
(* Standard ARM ABI: X0 = k, X1 = z, X2 = n, X3 = x                          *)
(*                                                                           *)
(* This file tries to prove the constant time property of bignum_copy()      *)
(* by stating the property for each basic block in the ensures_n form, then  *)
(* composes these triples to prove the full statement.                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/constant_time.ml";;

(**** print_literal_from_elf "arm/generic/bignum_copy.o";;
 ****)

let bignum_copy_mc = define_assert_from_elf "bignum_copy_mc" "arm/generic/bignum_copy.o" [
  0xeb02001f;       (* arm_CMP X0 X2 *)
  0x9a823002;       (* arm_CSEL X2 X0 X2 Condition_CC *)
  0xd2800004;       (* arm_MOV X4 (rvalue (word 0)) *)
  0xb40000c2;       (* arm_CBZ X2 (word 24) *)
  0xf8647865;       (* arm_LDR X5 X3 (Shiftreg_Offset X4 3) *)
  0xf8247825;       (* arm_STR X5 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb02009f;       (* arm_CMP X4 X2 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0xf824783f;       (* arm_STR XZR X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let COPY_EXEC = ARM_MK_EXEC_RULE bignum_copy_mc;;

let ITE_SAME = prove(`(if b then x else x) = x`, MESON_TAC []);;
let WORD64_MULT_MOD = prove(`forall x y. word (x * y MOD 2 EXP 64):int64 = word (x * y)`,
  ONCE_REWRITE_TAC[GSYM VAL_EQ] THEN REWRITE_TAC[VAL_WORD] THEN
  REWRITE_TAC[DIMINDEX_64] THEN CONV_TAC (ONCE_DEPTH_CONV MOD_DOWN_CONV)
  THEN REWRITE_TAC[]);;


let INIT_CONST_TIME = prove(
  `forall pc k z n x es.
    k < 2 EXP 64 /\ n < 2 EXP 64
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word pc /\
           C_ARGUMENTS [word k; z; word n; x] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
           (~(0 = MIN n k) /\ read PC s = word (pc + 0x10) \/ 0 = MIN n k /\ read PC s = word (pc + 0x24)) /\
           C_ARGUMENTS [word k; z; word (MIN n k); x; word 0] s /\
           read events s = CONS
            (EventJump (word (pc+12), word (pc + (if MIN n k = 0 then 36 else 16))))
            es)
      (\s s'. T)
      (\s. 4)`,
  let finish =
    IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT; ITE_SAME] THEN
    COND_CASES_TAC THENL replicate (
      ASM_REWRITE_TAC []) 2 THEN NO_TAC in
  IMP_REWRITE_TAC [C_ARGUMENTS; MIN] THEN
  REPEAT STRIP_TAC THEN
  ARM_N_SIM_TAC COPY_EXEC (1--4) THEN
  DISJ_CASES_TAC (SPEC `k < n` EXCLUDED_MIDDLE) THENL [
    ASSUME_TAC (ARITH_RULE `k < n ==> k <= n`) THEN
    ASSUME_TAC (ARITH_RULE `k < n ==> ~(n <= k)`) THEN
    finish;
    DISJ_CASES_TAC (SPEC `k:num = n` EXCLUDED_MIDDLE) THENL [
      finish;
      ASSUME_TAC (ARITH_RULE `~(k < n) /\ ~(k = n) ==> ~(k <= n)`) THEN
      ASSUME_TAC (ARITH_RULE `~(k < n) ==> n <= k`) THEN
      finish]]);;

let COPYLOOP_CONST_TIME = prove(
  `forall pc k z n x es.
    k < 2 EXP 64 /\ n < 2 EXP 64 /\ ~(0 = MIN n k) /\
    nonoverlapping (word pc, 0x40) (z, 8 * k)
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x10) /\
           C_ARGUMENTS [word k; z; word (MIN n k); x; word 0] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x24) /\
           C_ARGUMENTS [word k; z; word (MIN n k); x; word (MIN n k)] s /\
           read events s = APPEND
            (ENUMERATEL (MIN n k) (\i. [
              EventJump (word (pc+0x20), word (pc + (if i + 1 < MIN n k then 0x10 else 0x24)));
              EventStore (word_add z (word (8 * i)),8);
              EventLoad (word_add x (word (8 * i)),8)
            ]))
           es)
      (\s s'. T)
      (\s. 5 * MIN n k)`,
  REWRITE_TAC [C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_N_WHILE_PUP_TAC `MIN n k` `pc + 0x10` `pc + 0x20`
  `\i s.
      read X0 s = word k /\ read X1 s = z /\ read X2 s = word (MIN n k) /\
      read X3 s = x /\ read X4 s = word i /\
      read events s = APPEND
            (let es2 = ENUMERATEL i (\j. [
              EventJump (word (pc+0x20), word (pc + (if j + 1 < MIN n k then
                0x10 else 0x24)));
              EventStore (word_add z (word (8 * j)),8);
              EventLoad (word_add x (word (8 * j)),8)
            ]) in
            if read PC s = word (pc+0x20) then TL es2 else es2)
           es`
  `\(i:num) s. read CF s <=> MIN n k <= i`
  `\(i:num). 4`
  `0` `1` THEN
  REPEAT CONJ_TAC THENL [
    (* # loop itrs > 0 *)
    ASM_ARITH_TAC;
    (* entrace -> loop header *)
    MATCH_MP_TAC ENSURES_N_ALREADY THEN
    REWRITE_TAC[ENUMERATEL; LET_END_DEF; LET_DEF; subsumed] THEN
    REPEAT_N 2 STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    IMP_REWRITE_TAC[WORD64_NE_ADD2; APPEND] THEN
    ARITH_TAC;
    (* the main loop! *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word i:64 word) < k` ASSUME_TAC THENL
    [IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT]; ALL_TAC] THEN
    ARM_N_SIM_TAC COPY_EXEC (1--4) THEN
    SUBGOAL_THEN `k < 2 EXP 64 /\ n < 2 EXP 64 ==> MIN n k < 2 EXP 64` ASSUME_TAC THENL
    [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64;
                LET_DEF;LET_END_DEF] THEN
    CONJ_TAC THENL [
      ALL_TAC;
      IMP_REWRITE_TAC [MOD_LT; ARITH_RULE `i < MIN n k /\ MIN n k < 2 EXP 64 ==> i + 1 < 2 EXP 64`]
    ] THEN
    IMP_REWRITE_TAC[WORD64_NE_ADD2] THEN
    REWRITE_TAC[ARITH_RULE`i+1=SUC i`;ENUMERATEL;APPEND;TL] THEN
    REWRITE_TAC[WORD64_MULT_MOD] THEN ARITH_TAC;
    (* backedge *)
    REPEAT STRIP_TAC THEN
    ARM_N_SIM_TAC COPY_EXEC (1--1) THEN
    REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
    IMP_REWRITE_TAC[GSYM WORD_ADD;WORD64_NE_ADD2] THEN
    DISJ_CASES_TAC (SPEC `i:num` num_CASES) THENL
    [ ASM_ARITH_TAC; FIRST_X_ASSUM MP_TAC ] THEN
    STRIP_TAC THEN FIRST_ASSUM (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ENUMERATEL;APPEND;TL] THEN
    SUBGOAL_THEN `(n' + 1 < MIN n k) <=> true` (fun th -> REWRITE_TAC[th]) THENL
    [ SIMPLE_ARITH_TAC ; ARITH_TAC ];
    (* postcond to ret *)
    REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
    ARM_N_SIM_TAC COPY_EXEC (1--1) THEN
    DISJ_CASES_TAC (SPEC `MIN n k` num_CASES) THENL
    [ ASM_ARITH_TAC; FIRST_X_ASSUM MP_TAC ] THEN
    STRIP_TAC THEN FIRST_ASSUM (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ENUMERATEL;APPEND;TL] THEN
    REWRITE_TAC[ARITH_RULE`~(n' + 1 < SUC n')`] THEN
    NO_TAC;
    (* counter *)
    REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ASM_ARITH_TAC]);;

let PADDING_CONST_TIME = prove(
  `forall pc k z n x es.
    k < 2 EXP 64 /\ n < 2 EXP 64
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x24) /\
           C_ARGUMENTS [word k; z; word (MIN n k); x; word (MIN n k)] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
          (~(k <= MIN n k) /\ read PC s = word (pc + 0x2c) \/
           k <= MIN n k /\ read PC s = word (pc + 0x3c)) /\
          C_ARGUMENTS [word k; z; word (MIN n k); x; word (MIN n k)] s /\
          read events s = CONS
            (EventJump (word (pc+40), word (pc + (if k <= MIN n k then 0x3c else 44))))
            es)
      (\s s'. T)
      (\s. 2)`,
  REWRITE_TAC [C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MIN n k < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ARM_N_SIM_TAC COPY_EXEC (1--2) THEN
  DISJ_CASES_TAC (SPEC `k <= MIN n k` EXCLUDED_MIDDLE) THENL [
    IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT];
    IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    ASM_REWRITE_TAC [GSYM NOT_LE]]);;

let PADLOOP_CONST_TIME = prove(
  `forall pc k z n x es.
    k < 2 EXP 64 /\ n < 2 EXP 64 /\ ~(k <= MIN n k) /\
    nonoverlapping (word pc, 0x40) (z, 8 * k)
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x2c) /\
           C_ARGUMENTS [word k; z; word (MIN n k); x; word (MIN n k)] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x3c) /\
           read events s = APPEND (ENUMERATEL (k - MIN n k) (\i. [
            EventJump (word (pc+0x38), word (pc + (if (MIN n k + i) + 1 < k then 0x2c else 0x3c)));
            EventStore (word_add z (word (8 * ((MIN n k) + i))),8)
          ])) es)
      (\s s'. T)
      (\s. 4 * (k - (MIN n k)))`,
  REWRITE_TAC [C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_N_WHILE_PAUP_TAC `(MIN n k):num` `k:num` `pc + 0x2c` `pc + 0x38`
  `\i s.
      read X0 s = word k /\ read X1 s = z /\ read X2 s = word (MIN n k) /\ read X3 s = x /\ read X4 s = word i /\
      read events s = APPEND
        (let es2 = ENUMERATEL (i - MIN n k) (\j. [
            EventJump (word (pc+0x38), word (pc + (if (MIN n k + j) + 1 < k then 0x2c else 0x3c)));
            EventStore (word_add z (word (8 * ((MIN n k) + j))),8)
          ]) in
          if read PC s = word (pc + 0x38) then TL es2 else es2)
        es`
  `\(i:num) s. read CF s <=> k <= i`
  `\(i:num). 3`
  `0` `1` THEN
  REPEAT CONJ_TAC THENL [
    (* # loop itrs > 0 *)
    ASM_ARITH_TAC;
    (* entrace -> loop header *)
    MATCH_MP_TAC ENSURES_N_ALREADY THEN
    REWRITE_TAC[LET_DEF;LET_END_DEF;subsumed;SUB_REFL;ENUMERATEL] THEN
    REPEAT_N 2 STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN IMP_REWRITE_TAC[WORD64_NE_ADD2; APPEND] THEN
    ARITH_TAC;
    (* the main loop! *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word i:64 word) < k` ASSUME_TAC THENL [IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT]; ALL_TAC] THEN
    ARM_N_SIM_TAC COPY_EXEC (1--3) THEN
    REPEAT CONJ_TAC THENL [
      REWRITE_TAC[WORD_ADD];

      REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
      IMP_REWRITE_TAC[GSYM WORD_ADD;WORD64_NE_ADD2] THEN
      SUBGOAL_THEN `(i+1)-MIN n k = SUC(i- MIN n k)` SUBST_ALL_TAC THENL [
        UNDISCH_TAC `MIN n k <= i` THEN ARITH_TAC; ALL_TAC
      ] THEN
      REWRITE_TAC[ENUMERATEL;TL;APPEND] THEN
      REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
      SUBGOAL_THEN `MIN n k + i - MIN n k = i` SUBST_ALL_TAC THENL [
        UNDISCH_TAC `MIN n k <= i` THEN ARITH_TAC; ALL_TAC
      ] THEN
      IMP_REWRITE_TAC[MOD_LT] THEN ARITH_TAC;

      REWRITE_TAC [VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
      IMP_REWRITE_TAC [MOD_LT; ARITH_RULE `i < n /\ n < 2 EXP 64 ==> i + 1 < 2 EXP 64`];
    ];
    (* backedge *)
    REPEAT STRIP_TAC THEN
    ARM_N_SIM_TAC COPY_EXEC (1--1) THEN
    REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
    IMP_REWRITE_TAC[GSYM WORD_ADD;WORD64_NE_ADD2] THEN
    DISJ_CASES_TAC (SPEC `i - MIN n k` num_CASES) THENL
    [ ASM_ARITH_TAC; FIRST_X_ASSUM MP_TAC ] THEN
    STRIP_TAC THEN FIRST_ASSUM (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ENUMERATEL;APPEND;TL] THEN

    COND_CASES_TAC THENL [ REWRITE_TAC[] THEN ARITH_TAC; SIMPLE_ARITH_TAC ];
    (* postcond to ret *)
    ARM_N_SIM_TAC COPY_EXEC (1--1) THEN
    REWRITE_TAC[LET_DEF;LET_END_DEF] THEN
    DISJ_CASES_TAC (SPEC `k - MIN n k` num_CASES) THENL
    [ ASM_ARITH_TAC; FIRST_X_ASSUM MP_TAC ] THEN
    STRIP_TAC THEN FIRST_ASSUM (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[ENUMERATEL;APPEND;TL] THEN
    COND_CASES_TAC THENL [ SIMPLE_ARITH_TAC; REWRITE_TAC[] ];

    (* counter *)
    REWRITE_TAC [NSUM_CONST_NUMSEG] THEN ASM_ARITH_TAC]);;


(* The full event trace of the bignum_copy function. It is parameteric to
   public data k, z, n, x and pc (the program counter). Note that z and x are
   addresses to the buffers, not their contents.
   Note that this definition is equivalent to the events definition in
   bignum_copy.fn_and_const_combined.ml . *)

let events = `\k z n x pc. APPEND
  (ENUMERATEL (k - MIN n k)
    (\i. [
      EventJump (
        word (pc+0x38), word (pc+(if (MIN n k + i) + 1 < k then 0x2c else 0x3c)));
      EventStore (word_add z (word (8 * ((MIN n k) + i))),8)
    ]))
  (APPEND
    [EventJump (
      word (pc+0x28), word (pc+(if (k <= MIN n k) then 0x3c else 0x2c)))]
    (APPEND
      (ENUMERATEL (MIN n k)
        (\i. [EventJump (
                word (pc+0x20), word (pc+(if (i + 1 < MIN n k) then 0x10 else 0x24)));
              EventStore (word_add z (word (8 * i)),8);
              EventLoad (word_add x (word (8 * i)),8)
        ]))
      [EventJump (
        word (pc+0xc), word (pc+(if MIN n k = 0 then 0x24 else 0x10)))]
    )
  )`;;

let get_event_trace_expr (the_goal:term) =
  let the_const,(_::apre::_) = strip_comb the_goal in
  let prevar,prebody = dest_abs apre in
  let conjs = conjuncts prebody in
  let lastconj = last conjs in
  let the_event_list = rhs lastconj in
  the_event_list;;

(* Split {P} C {Q} to {P} C {R} C' {Q}, and match spec_th to
   {P} C {R}, leaving {R} C' {Q} only. *)

let SEQ_HOARE_TRIPLE_TAC spec_th =
  ONCE_REWRITE_TAC [GSYM (INST_TYPE [`:armstate`, `:B`] COMPONENT_SINK)] THEN
  MATCH_MP_TAC ENSURES_N_TRANS THEN
  META_EXISTS_TAC THEN
  CONJ_TAC THENL [
    (fun (asl,w) ->
      MP_TAC (SPECL [`pc:num`;`k:num`;`z:int64`;`n:num`;`x:int64`;
                     get_event_trace_expr w]
          spec_th) (asl,w)) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (UNIFY_ACCEPT_TAC [`Q:armstate->bool`]);

    ALL_TAC];;

(* Given {P} C {Q}, match spec_th to the goal. *)

let FINAL_HOARE_TRIPLE_TAC spec_th =
  ASM_REWRITE_TAC[] THEN
  (fun (asl,w) ->
    MP_TAC (SPECL [`pc:num`;`k:num`;`z:int64`;`n:num`;`x:int64`;
                    get_event_trace_expr w]
        spec_th) (asl,w)) THEN
  ASM_REWRITE_TAC[SUB_0;ENUMERATEL;APPEND; GSYM APPEND_ASSOC; ADD] THEN
  NO_TAC;;


let BIGNUM_COPY_CONSTTIME = prove(
  `exists f_es. forall pc k z n x.
    k < 2 EXP 64 /\ n < 2 EXP 64 /\
    nonoverlapping (word pc, 0x40) (z, 8 * k)
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word pc /\
           C_ARGUMENTS [word k; z; word n; x] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x3c) /\
           read events s = APPEND (f_es k z n x pc) es)
      (\s s'. T)
      (\s. 4 + 5 * MIN n k + 2 + 4 * (k - (MIN n k)))`,
  EXISTS_TAC events THEN
  REPEAT STRIP_TAC THEN

  SEQ_HOARE_TRIPLE_TAC INIT_CONST_TIME THEN

  DISJ_CASES_TAC (SPEC `MIN n k = 0` EXCLUDED_MIDDLE) THENL [
    ASM_REWRITE_TAC[SUB_0; MULT_0; ADD] THEN
    SEQ_HOARE_TRIPLE_TAC PADDING_CONST_TIME THEN
    DISJ_CASES_TAC (SPEC `k <= 0` EXCLUDED_MIDDLE) THENL [
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `k=0` SUBST_ALL_TAC THENL [ ASM_ARITH_TAC; ALL_TAC ] THEN
      REWRITE_TAC[MULT_0;ENUMERATEL;APPEND;ARITH_RULE`MIN x 0 = 0`;SUB_REFL;
                  LE_REFL] THEN
      MATCH_MP_TAC ENSURES_N_ALREADY THEN REWRITE_TAC[subsumed] THEN MESON_TAC[];

      FINAL_HOARE_TRIPLE_TAC PADLOOP_CONST_TIME
    ];

    ASM_REWRITE_TAC[SUB_0; MULT_0] THEN
    SEQ_HOARE_TRIPLE_TAC COPYLOOP_CONST_TIME THEN
    SEQ_HOARE_TRIPLE_TAC PADDING_CONST_TIME THEN

    DISJ_CASES_TAC (SPEC `k <= MIN n k` EXCLUDED_MIDDLE) THENL [
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `k - MIN n k = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MULT_0;ENUMERATEL;APPEND;GSYM APPEND_ASSOC] THEN
      MATCH_MP_TAC ENSURES_N_ALREADY THEN REWRITE_TAC[subsumed] THEN MESON_TAC[];

      FINAL_HOARE_TRIPLE_TAC PADLOOP_CONST_TIME
    ]
  ]);;

Printf.printf "(CAV25) BIGNUM_COPY_CONSTTIME (ensures_n version) proven correct: %s\n"
  (string_of_thm BIGNUM_COPY_CONSTTIME);;