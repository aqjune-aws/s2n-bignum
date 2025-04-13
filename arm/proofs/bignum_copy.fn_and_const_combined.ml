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
(* This file tries to prove the combined statement of functional correctness *)
(* and constant time properties at once, then induce the original functional *)
(* correctness statements of bignum_copy.ml and also the constant time prop- *)
(* erty statement in the relational Hoare triple form.                       *)
(* ========================================================================= *)

needs "arm/proofs/base.ml";;
needs "arm/proofs/equiv.ml";;
needs "arm/proofs/constant_time.ml";;

(**** print_literal_from_elf "arm/generic/bignum_copy.o";;
 ****)

let bignum_copy_mc =
  define_assert_from_elf "bignum_copy_mc" "arm/generic/bignum_copy.o"
[
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

let BIGNUM_COPY_EXEC = ARM_MK_EXEC_RULE bignum_copy_mc;;

(* ------------------------------------------------------------------------- *)
(* Functional correctness + constant-time property proof.                    *)
(* ------------------------------------------------------------------------- *)

(* The full event trace of the bignum_copy function. It is parameteric to
   public data k, z, n, x and pc (the program counter). Note that z and x are
   addresses to the buffers, not their contents.
   Note that this definition is equivalent to the events definition in
   bignum_copy.constant_time_ensures_n.ml .  *)

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

(* Tactics that helps simplifying event traces. *)

let SIMPLIFY_EVENT_TRACE_TAC =
  REPEAT (CHANGED_TAC (
    TRY (IMP_REWRITE_TAC[GSYM WORD_ADD; WORD64_NE_ADD2] THEN CONJ_TAC
    THENL [ALL_TAC; ARITH_TAC]) THEN
    REWRITE_TAC[LET_DEF;LET_END_DEF;ENUMERATEL;ENUMERATEL_ADD1;TL;APPEND]));;

let SIMPLIFY_TRACE_AND_DESTRUCT_NUM_TAC inum =
  SIMPLIFY_EVENT_TRACE_TAC THEN
  DISJ_CASES_TAC (SPEC inum num_CASES) THENL [
    (*FIRST_X_ASSUM MP_TAC THEN UNDISCH_TAC asmnonzero THEN ARITH_TAC*)
    SIMPLE_ARITH_TAC; ALL_TAC
  ] THEN
  FIRST_X_ASSUM MP_TAC THEN DISCH_THEN (STRIP_THM_THEN
    (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th)) THEN
  SIMPLIFY_EVENT_TRACE_TAC;;

let BIGNUM_COPY_CORRECT_AND_CONSTTIME = prove
 (`exists f_es. forall k z n x a pc (es:armevent list).
     nonoverlapping (word pc,0x40) (z,8 * val k) /\
     (x = z \/ nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures_n arm
           (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
                read PC s = word pc /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a /\
                read events s = es)
           (\s. read PC s = word (pc + 0x3c) /\
                bignum_from_memory (z,val k) s = lowdigits a (val k) /\
                read events s = APPEND (f_es (val k) z (val n) x pc) es)
           (MAYCHANGE [PC; X2; X4; X5] ,, MAYCHANGE SOME_FLAGS ,,
            MAYCHANGE [memory :> bignum(z,val k)] ,,
            MAYCHANGE [events])
           (\s. 4 * val k + MIN (val n) (val k) + 6)`,
  (* Instantiate with the events *)
  EXISTS_TAC events THEN
  (* Break the number of steps expression into addition of expressions for each
     block. *)
  REWRITE_TAC[ARITH_RULE
    `forall n k. 4 * k + MIN n k + 6 = 3 + (1 + 5 * MIN n k) + 2 + 4 * (k - (MIN n k))`]
  THEN

  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_COPY_EXEC] THEN
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `pc:num`; `es:armevent list`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN

  (*** Simulate the initial computation of min(n,k) and then
   *** recast the problem with n' = min(n,k) so we can assume
   *** hereafter that n <= k. This makes life a bit easier since
   *** otherwise n can actually be any number < 2^64 without
   *** violating the preconditions.
   ***)

  ENSURES_N_SEQUENCE_TAC `pc + 0xc`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X2 s = word(MIN n k) /\
        read X3 s = x /\
        read X4 s = word 0 /\
        bignum_from_memory (x,MIN n k) s = lowdigits a k /\
        read events s = es`
    `3` `4 * k + MIN n k + 3` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM LOWDIGITS_BIGNUM_FROM_MEMORY] THEN
    ARM_N_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
    REWRITE_TAC[ARITH_RULE `MIN n k = if k < n then k else n`] THEN
    MESON_TAC[];
    ALL_TAC;
    ARITH_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (vfree_in `k:num` o concl))) THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN MP_TAC(ARITH_RULE `MIN n k <= k`) THEN
  SPEC_TAC(`lowdigits a k`,`a:num`) THEN SPEC_TAC(`MIN n k`,`n:num`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  VAL_INT64_TAC `n:num` THEN ENSURES_N_BIGNUM_RANGE_TAC "n" "a" THEN

  (*** Break at the start of the padding stage ***)
  ENSURES_N_SEQUENCE_TAC `pc + 0x24`
   `\s. read X0 s = word k /\
        read X1 s = z /\
        read X4 s = word n /\
        bignum_from_memory(z,n) s = a /\
        read events s = APPEND (APPEND (ENUMERATEL n
            (\i. [EventJump (word (pc+0x20),
                             word (pc+(if i + 1 < n then 0x10 else 0x24)));
                  EventStore (word_add z (word (8 * i)),8);
                  EventLoad (word_add x (word (8 * i)),8)]))
          [EventJump (
            word (pc+0xc),word (pc+(if n = 0 then 0x24 else 0x10)))]) es`
    `1 + 5 * n` `2 + 4 * (k - MIN n k)` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `n = 0` THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL] THEN
      REWRITE_TAC[MESON[] `0 = a <=> a = 0`; ARITH_RULE `1 + 5 * 0 = 1`] THEN
      REWRITE_TAC[ARITH_RULE `MIN 0 k = 0 /\ 0 = 0`; ENUMERATEL; APPEND] THEN
      ARM_N_SIM_TAC BIGNUM_COPY_EXEC [1];
      ALL_TAC] THEN

    FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

    (*** The main copying loop, in the case when n is nonzero ***)

    ENSURES_N_WHILE_UP_TAC `n:num` `pc + 0x10` `pc + 0x1c`
     `\i s. read X0 s = word k /\
            read X1 s = z /\
            read X2 s = word n /\
            read X3 s = x /\
            read X4 s = word i /\
            bignum_from_memory(z,i) s = lowdigits a i /\
            bignum_from_memory(word_add x (word(8 * i)),n - i) s = highdigits a i /\
            read events s = APPEND (APPEND
              (let es2 = ENUMERATEL i (\j. [
                  EventJump (word (pc+0x20), word (pc+(if j + 1 < n then 0x10 else 0x24)));
                  EventStore (word_add z (word (8 * j)),8);
                  EventLoad (word_add x (word (8 * j)),8)]) in
              if read PC s = word (pc + 0x1c) then TL es2 else es2)
              [EventJump (
                word (pc+0xc),word (pc+(if n = 0 then 0x24 else 0x10)))]) es`
      `(\i:num. 3)` `1` `2` `2` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARM_N_SIM_TAC BIGNUM_COPY_EXEC [1] THEN
      REWRITE_TAC[SUB_0; GSYM BIGNUM_FROM_MEMORY_BYTES; HIGHDIGITS_0] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_TRIVIAL; MULT_CLAUSES; WORD_ADD_0] THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES; LOWDIGITS_0] THEN
      SIMPLIFY_EVENT_TRACE_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV)
       [BIGNUM_FROM_MEMORY_OFFSET_EQ_HIGHDIGITS] THEN
      ASM_REWRITE_TAC[SUB_EQ_0; GSYM NOT_LT] THEN
      REWRITE_TAC[ARITH_RULE `k - i - 1 = k - (i + 1)`] THEN
      REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
      ARM_N_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
      ASM_REWRITE_TAC[GSYM WORD_ADD; VAL_WORD_BIGDIGIT] THEN
      REWRITE_TAC[LOWDIGITS_CLAUSES] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      SIMPLIFY_EVENT_TRACE_TAC;
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ARM_N_SIM_TAC ~rewrite_read_pc:true BIGNUM_COPY_EXEC (1--2) THEN
      SIMPLIFY_TRACE_AND_DESTRUCT_NUM_TAC `i:num` THEN
      COND_CASES_TAC THEN SIMPLE_ARITH_TAC;

      ARM_N_SIM_TAC ~rewrite_read_pc:true BIGNUM_COPY_EXEC (1--2) THEN
      ASM_SIMP_TAC[LOWDIGITS_SELF] THEN
      SIMPLIFY_TRACE_AND_DESTRUCT_NUM_TAC `n:num` THEN
      COND_CASES_TAC THEN SIMPLE_ARITH_TAC;

      REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ASM_ARITH_TAC;
    ];

    CONJ_TAC THENL [ALL_TAC; ASM_ARITH_TAC]
  ] THEN

  FIRST_X_ASSUM(DISJ_CASES_THEN2 SUBST_ALL_TAC ASSUME_TAC o
    MATCH_MP (ARITH_RULE `n:num <= k ==> n = k \/ n < k`)) THENL
   [SUBST1_TAC (ARITH_RULE `2 + 4 * (k - MIN k k) = 2`) THEN
    ARM_N_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
    REWRITE_TAC [ENUMERATEL; APPEND] THEN NO_TAC;
    ALL_TAC] THEN

  FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
      NONOVERLAPPING_IMP_SMALL_2)) THEN
    ANTS_TAC THENL [SIMPLE_ARITH_TAC; DISCH_TAC] THEN

  (*** Main padding loop ***)

  SUBGOAL_THEN `~(k:num <= n)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NOT_LE]; ALL_TAC] THEN

  (*** Simplifying events ***)

  REWRITE_TAC [GSYM APPEND_ASSOC] THEN
  SPEC_TAC(`APPEND (ENUMERATEL n (\i. [EventJump (word (pc + 32), word (pc + (if i + 1 < n then 16 else 36)));
                                       EventStore (word_add z (word (8 * i)), 8);
                                       EventLoad (word_add x (word (8 * i)), 8)]))
                   (APPEND [EventJump (word (pc + 12), word (pc + (if n = 0 then 36 else 16)))] es)`,`es:armevent list`) THEN
  GEN_TAC THEN

  ENSURES_N_WHILE_AUP_TAC `n:num` `k:num` `pc + 0x2c` `pc + 0x34`
   `\i s. read X0 s = word k /\
          read X1 s = z /\
          read X4 s = word i /\
          bignum_from_memory(z,i) s = a /\
          read events s = APPEND
            (let es2 = ENUMERATEL (i - n) (\j. [EventJump (word (pc + 56), word (pc + (if (n + j) + 1 < k then 44 else 60)));
                EventStore (word_add z (word (8 * (n + j))),8)]) in
             if read PC s = word (pc + 0x34) then TL es2 else es2)
            (APPEND [EventJump (word (pc + 40), word (pc + (if k <= n then 60 else 44)))] es)`
   `(\i:num. 2)` `2` `2` `2` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `n - n = 0`; ENUMERATEL; APPEND] THEN
    ARM_N_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
    SIMPLIFY_EVENT_TRACE_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_STEP] THEN
    ARM_N_SIM_TAC BIGNUM_COPY_EXEC (1--2) THEN
    REWRITE_TAC[VAL_WORD_0; MULT_CLAUSES; ADD_CLAUSES; WORD_ADD] THEN
    SUBGOAL_THEN `(i+1)-n = SUC (i-n)` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC;ALL_TAC] THEN
    SIMPLIFY_EVENT_TRACE_TAC THEN
    SUBGOAL_THEN `n + i - n = i` SUBST_ALL_TAC THENL [SIMPLE_ARITH_TAC; ALL_TAC]
    THEN REWRITE_TAC[] THEN NO_TAC;

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
    ARM_N_SIM_TAC ~rewrite_read_pc:true BIGNUM_COPY_EXEC (1--2) THEN
    SIMPLIFY_TRACE_AND_DESTRUCT_NUM_TAC `i-n` THEN
    SUBGOAL_THEN `((n + n') + 1 < k) <=> true` MP_TAC THENL
    [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[] THEN NO_TAC;

    ARM_N_SIM_TAC ~rewrite_read_pc:true BIGNUM_COPY_EXEC (1--2) THEN
    SIMPLIFY_TRACE_AND_DESTRUCT_NUM_TAC `k-n` THEN
    SUBGOAL_THEN `((n + n') + 1 < k) <=> false` MP_TAC THENL [SIMPLE_ARITH_TAC;ALL_TAC]
    THEN DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[] THEN NO_TAC;

    REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ASM_ARITH_TAC
  ]);;

Printf.printf "BIGNUM_COPY_CORRECT_AND_CONSTTIME proven correct: %s\n"
  (string_of_thm BIGNUM_COPY_CORRECT_AND_CONSTTIME);;

(* ------------------------------------------------------------------------- *)
(* Inducing multiple variants of functional correctness proofs from the      *)
(* functional correctness + constant-time property proof.                    *)
(* The 'ensures' variants of functional correctnesses are syntactically equal*)
(* to those in bignum_copy.ml.                                               *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_COPY_CORRECT = prove
 (`forall k z n x a pc.
 nonoverlapping (word pc,0x40) (z,8 * val k) /\
 (x = z \/ nonoverlapping (x,8 * MIN (val n) (val k)) (z,8 * val k))
 ==> ensures_n arm
       (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
            read PC s = word pc /\
            C_ARGUMENTS [k; z; n; x] s /\
            bignum_from_memory (x,val n) s = a)
       (\s. read PC s = word (pc + 0x3c) /\
            bignum_from_memory (z,val k) s = lowdigits a (val k))
       (MAYCHANGE [PC; X2; X4; X5] ,, MAYCHANGE SOME_FLAGS ,,
        MAYCHANGE [memory :> bignum(z,val k)] ,,
        MAYCHANGE [events])
       (\s. 4 * val k + MIN (val n) (val k) + 6)`,
  DROP_EVENTS_COND_TAC BIGNUM_COPY_CORRECT_AND_CONSTTIME);;

let BIGNUM_COPY_SUBROUTINE_CORRECT_ENSURESN = prove
 (`forall k z n x a pc returnaddress.
     nonoverlapping (word pc,0x40) (z,8 * val k) /\
     (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures_n arm
           (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc  /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,val k) s =  lowdigits a (val k))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val k)])
           (\s. 4 * val k + MIN (val n) (val k) + 7)`,
  REWRITE_TAC[ARITH_RULE `a + b + 7 = (a + b + 6) + 1`] THEN
  ARM_N_ADD_RETURN_NOSTACK_TAC BIGNUM_COPY_EXEC BIGNUM_COPY_CORRECT);;

let BIGNUM_COPY_SUBROUTINE_CORRECT_ORIGINAL = prove
 (`forall k z n x a pc returnaddress.
     nonoverlapping (word pc,0x40) (z,8 * val k) /\
     (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
     ==> ensures arm
           (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc  /\
                read PC s = word pc /\
                read X30 s = returnaddress /\
                C_ARGUMENTS [k; z; n; x] s /\
                bignum_from_memory (x,val n) s = a)
           (\s. read PC s = returnaddress /\
                bignum_from_memory (z,val k) s =  lowdigits a (val k))
           (MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
            MAYCHANGE [memory :> bignum(z,val k)])`,
  ENSURES_N_ENSURES_TAC BIGNUM_COPY_SUBROUTINE_CORRECT_ENSURESN);;

Printf.printf "BIGNUM_COPY_SUBROUTINE_CORRECT_ORIGINAL proven correct: %s\n"
  (string_of_thm BIGNUM_COPY_SUBROUTINE_CORRECT_ORIGINAL);;


(* ------------------------------------------------------------------------- *)
(* Inducing the ensures2 version of constant-time proof from the functional  *)
(* correctness + constant-time property proof.                               *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_COPY_CONSTTIME = prove
 (`exists f_es. forall k:int64 z:int64 n:int64 x:int64 a1:num a2:num pc1 pc2 es1 es2.
    nonoverlapping (word pc1,0x40) (z,8 * val k) /\ nonoverlapping (word pc2,0x40) (z,8 * val k) /\
    (x = z \/ nonoverlapping(x,8 * MIN (val n) (val k)) (z,8 * val k))
    ==>
    ensures2 arm
      (\(s1,s2). aligned_bytes_loaded s1 (word pc1) bignum_copy_mc /\ read PC s1 = word pc1 /\
                 aligned_bytes_loaded s2 (word pc2) bignum_copy_mc /\ read PC s2 = word pc2 /\
                 C_ARGUMENTS [k; z; n; x] s1 /\ C_ARGUMENTS [k; z; n; x] s2 /\
                 bignum_from_memory (x,val n) s1 = a1 /\ bignum_from_memory (x,val n) s2 = a2 /\
                 read events s1 = es1 /\ read events s2 = es2)
      (\(s1,s2). read PC s1 = word (pc1 + 0x3c) /\ read PC s2 = word (pc2 + 0x3c) /\
                 bignum_from_memory (z,val k) s1 = lowdigits a1 (val k) /\ bignum_from_memory (z,val k) s2 = lowdigits a2 (val k) /\
                 read events s1 = APPEND (f_es (val k) z (val n) x pc1) es1 /\
                 read events s2 = APPEND (f_es (val k) z (val n) x pc2) es2)
      (\(s1,s2) (s1',s2').
        (MAYCHANGE [PC; X2; X4; X5] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bignum(z,val k)] ,, MAYCHANGE [events]) s1 s1' /\
        (MAYCHANGE [PC; X2; X4; X5] ,, MAYCHANGE SOME_FLAGS ,, MAYCHANGE [memory :> bignum(z,val k)] ,, MAYCHANGE [events]) s2 s2')
      (\s. 4 * val k + MIN (val n) (val k) + 6)
      (\s. 4 * val k + MIN (val n) (val k) + 6)`,
  DESTRUCT_TAC "@f_es. H" BIGNUM_COPY_CORRECT_AND_CONSTTIME THEN
  EXISTS_TAC `f_es:num->int64->num->int64->num->armevent list` THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  USE_THEN "H" (MP_TAC o ISPECL [`k:int64`; `z:int64`; `n:int64`; `x:int64`; `a2:num`; `pc2:num`; `es2:armevent list`]) THEN
  REMOVE_THEN "H" (MP_TAC o ISPECL [`k:int64`; `z:int64`; `n:int64`; `x:int64`; `a1:num`; `pc1:num`; `es1:armevent list`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (fun th -> DISCH_THEN (MP_TAC o MATCH_MP COMBINE_ENSURES_N_ENSURES2 o CONJ th)) THEN
  MATCH_MP_TAC ENSURES2_WEAKEN THEN SIMP_TAC[SUBSUMED_REFL]);;

Printf.printf "BIGNUM_COPY_CONSTTIME (ensures2 version) proven correct: %s\n"
  (string_of_thm BIGNUM_COPY_CONSTTIME);;
