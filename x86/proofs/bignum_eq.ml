(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Equality test on bignums.                                                 *)
(* ========================================================================= *)

needs "x86/proofs/base.ml";;

(**** print_literal_from_elf "x86/generic/bignum_eq.o";;
 ****)

let bignum_eq_mc =
  define_assert_from_elf "bignum_eq_mc" "x86/generic/bignum_eq.o"
[
  0xf3; 0x0f; 0x1e; 0xfa;  (* ENDBR64 *)
  0x48; 0x31; 0xc0;        (* XOR (% rax) (% rax) *)
  0x48; 0x39; 0xd7;        (* CMP (% rdi) (% rdx) *)
  0x73; 0x18;              (* JAE (Imm8 (word 24)) *)
  0x48; 0xff; 0xca;        (* DEC (% rdx) *)
  0x48; 0x0b; 0x04; 0xd1;  (* OR (% rax) (Memop Quadword (%%% (rcx,3,rdx))) *)
  0x48; 0x39; 0xd7;        (* CMP (% rdi) (% rdx) *)
  0x75; 0xf4;              (* JNE (Imm8 (word 244)) *)
  0xeb; 0x0c;              (* JMP (Imm8 (word 12)) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x48; 0x0b; 0x04; 0xfe;  (* OR (% rax) (Memop Quadword (%%% (rsi,3,rdi))) *)
  0x48; 0x39; 0xd7;        (* CMP (% rdi) (% rdx) *)
  0x75; 0xf4;              (* JNE (Imm8 (word 244)) *)
  0x48; 0x85; 0xff;        (* TEST (% rdi) (% rdi) *)
  0x74; 0x12;              (* JE (Imm8 (word 18)) *)
  0x48; 0x8b; 0x54; 0xfe; 0xf8;
                           (* MOV (% rdx) (Memop Quadword (%%%% (rsi,3,rdi,-- &8))) *)
  0x48; 0x33; 0x54; 0xf9; 0xf8;
                           (* XOR (% rdx) (Memop Quadword (%%%% (rcx,3,rdi,-- &8))) *)
  0x48; 0x09; 0xd0;        (* OR (% rax) (% rdx) *)
  0x48; 0xff; 0xcf;        (* DEC (% rdi) *)
  0x75; 0xee;              (* JNE (Imm8 (word 238)) *)
  0x48; 0xf7; 0xd8;        (* NEG (% rax) *)
  0x48; 0x19; 0xc0;        (* SBB (% rax) (% rax) *)
  0x48; 0xff; 0xc0;        (* INC (% rax) *)
  0xc3                     (* RET *)
];;

let bignum_eq_tmc = define_trimmed "bignum_eq_tmc" bignum_eq_mc;;

let BIGNUM_EQ_EXEC = X86_MK_CORE_EXEC_RULE bignum_eq_tmc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_EQ_CORRECT = prove
 (`forall m a x n b y pc.
        ensures x86
          (\s. bytes_loaded s (word pc) (BUTLAST bignum_eq_tmc) /\
               read RIP s = word pc /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read RIP s' = word (pc + 0x42) /\
                C_RETURN s' = if x = y then word 1 else word 0)
          (MAYCHANGE [RIP; RDI; RDX; RCX; RAX] ,,
           MAYCHANGE SOME_FLAGS ,, MAYCHANGE [events])`,
  W64_GEN_TAC `m:num` THEN MAP_EVERY X_GEN_TAC [`a:int64`; `x:num`] THEN
  W64_GEN_TAC `n:num` THEN MAP_EVERY X_GEN_TAC [`b:int64`; `y:num`] THEN
  X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS; fst BIGNUM_EQ_EXEC] THEN
  BIGNUM_RANGE_TAC "m" "x" THEN BIGNUM_RANGE_TAC "n" "y" THEN

  (*** Split into subgoals at "mmain" label and do the second part first ***)

  ABBREV_TAC `p = MIN m n` THEN VAL_INT64_TAC `p:num` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x22`
   `\s. read RDI s = word p /\
        read RSI s = a /\
        read RCX s = b /\
        bignum_from_memory (a,m) s = x /\
        bignum_from_memory (b,n) s = y /\
        (read RAX s = word 0 <=> highdigits x p = highdigits y p)` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    ASM_CASES_TAC `p = 0` THENL
     [ASM_REWRITE_TAC[HIGHDIGITS_0] THEN
      GHOST_INTRO_TAC `d:int64` `read RAX` THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EQ_EXEC (1--5) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_RULE;
      ALL_TAC] THEN

    ENSURES_WHILE_PDOWN_TAC `p:num` `pc + 0x27` `pc + 0x37`
     `\i s. (read RDI s = word i /\
             read RSI s = a /\
             read RCX s = b /\
             bignum_from_memory (a,m) s = x /\
             bignum_from_memory (b,n) s = y /\
             (read RAX s = word 0 <=> highdigits x i = highdigits y i)) /\
            (read ZF s <=> i = 0)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EQ_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[HIGHDIGITS_0; BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `d:int64` `read RAX` THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_EQ_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_SUB_0; VAL_EQ_0] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
      CONV_TAC WORD_RULE] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `i:num < m /\ i < n` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `i + 1`] THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (i + 1)) (word 1):int64 = word i`) THEN
    GHOST_INTRO_TAC `d:int64` `read RAX` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read(memory :>
           bytes64(word_add a (word(8 * (i + 1) + 18446744073709551608)))) s0 =
      word(bigdigit x i) /\
      read(memory :>
           bytes64(word_add b (word(8 * (i + 1) + 18446744073709551608)))) s0 =
      word(bigdigit y i)`
    ASSUME_TAC THENL
     [REWRITE_TAC[WORD_INDEX_WRAP] THEN MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                  BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      ASM_REWRITE_TAC[WORD_VAL];
      ALL_TAC] THEN
    X86_STEPS_TAC BIGNUM_EQ_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN
    GEN_REWRITE_TAC (RAND_CONV o BINOP_CONV) [HIGHDIGITS_STEP] THEN
    SIMP_TAC[LEXICOGRAPHIC_EQ_64; BIGDIGIT_BOUND] THEN
    AP_TERM_TAC THEN REWRITE_TAC[WORD_XOR_EQ_0] THEN
    MATCH_MP_TAC WORD_EQ_IMP THEN
    REWRITE_TAC[DIMINDEX_64; BIGDIGIT_BOUND]] THEN

  (*** The case m = n, which is a simple drop-through ***)

  ASM_CASES_TAC `m:num = n` THENL
   [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `MIN n n = p ==> p = n`)) THEN
    ASM_SIMP_TAC[HIGHDIGITS_ZERO] THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EQ_EXEC (1--4) THEN
    ENSURES_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[WORD_SUB_REFL; VAL_WORD_0];
    ALL_TAC] THEN

  (*** Now the n > m and m > n cases respectively, very similar proofs ***)

  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(m:num = n) ==> m < n \/ n < m`)) THEN
  UNDISCH_TAC `MIN m n = p` THEN
  ASM_SIMP_TAC[ARITH_RULE `m < n ==> MIN m n = m`;
               ARITH_RULE `n < m ==> MIN m n = n`] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_SIMP_TAC[HIGHDIGITS_ZERO] THENL
   [ENSURES_WHILE_PDOWN_TAC `n - m:num` `pc + 0x8` `pc + 0x12`
     `\i s. (read RDI s = word m /\
             read RSI s = a /\
             read RDX s = word(m + i) /\
             read RCX s = b /\
             bignum_from_memory (a,m) s = x /\
             bignum_from_memory (b,n) s = y /\
             (read RAX s = word 0 <=> highdigits y (m + i) = 0)) /\
            (read ZF s <=> i = 0)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `m:num < n` THEN ARITH_TAC;
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EQ_EXEC (1--3) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[GSYM NOT_LT; ARITH_RULE `m:num < n ==> m + n - m = n`] THEN
      ASM_SIMP_TAC[HIGHDIGITS_ZERO];
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `d:int64` `read RAX` THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_EQ_EXEC (1--2) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      MESON_TAC[]] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (m + i + 1)) (word 1):int64 = word(m + i)`) THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `m + i:num`] THEN
    GHOST_INTRO_TAC `d:int64` `read RAX` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add b (word (8 * (m + i))))) s0 =
      word(bigdigit y (m + i))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "y" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                  BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_VAL] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC BIGNUM_EQ_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN
    REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0;
      WORD_RULE `word_sub (word m) (word (m + i)) = word_neg(word i)`] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HIGHDIGITS_STEP] THEN
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
    REWRITE_TAC[DIMINDEX_64; BIGDIGIT_BOUND];

    ENSURES_WHILE_PDOWN_TAC `m - n:num` `pc + 0x16` `pc + 0x20`
     `\i s. (read RDI s = word(n + i) /\
             read RSI s = a /\
             read RDX s = word n /\
             read RCX s = b /\
             bignum_from_memory (a,m) s = x /\
             bignum_from_memory (b,n) s = y /\
             (read RAX s = word 0 <=> highdigits x (n + i) = 0)) /\
            (read ZF s <=> i = 0)` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `n:num < m` THEN ARITH_TAC;
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN
      SUBGOAL_THEN `n:num <= m` ASSUME_TAC THENL
       [ASM_SIMP_TAC[LT_IMP_LE]; ALL_TAC] THEN
      X86_STEPS_TAC BIGNUM_EQ_EXEC (1--4) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[ARITH_RULE `m:num < n ==> m + n - m = n`] THEN
      ASM_SIMP_TAC[HIGHDIGITS_ZERO; VAL_EQ_0; WORD_SUB_EQ_0] THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN SIMPLE_ARITH_TAC;
      ALL_TAC; (*** Main loop invariant ***)
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      ENSURES_INIT_TAC "s0" THEN X86_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
      GHOST_INTRO_TAC `d:int64` `read RAX` THEN ENSURES_INIT_TAC "s0" THEN
      X86_STEPS_TAC BIGNUM_EQ_EXEC [1] THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (n + i + 1)) (word 1):int64 = word(n + i)`) THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `n + i:num`] THEN
    GHOST_INTRO_TAC `d:int64` `read RAX` THEN
    REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN
    ENSURES_INIT_TAC "s0" THEN
    SUBGOAL_THEN
     `read(memory :> bytes64(word_add a (word (8 * (n + i))))) s0 =
      word(bigdigit x (n + i))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "x" THEN
      REWRITE_TAC[GSYM BIGNUM_FROM_MEMORY_BYTES;
                  BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_VAL] THEN SIMPLE_ARITH_TAC;
      ALL_TAC] THEN
    X86_STEPS_TAC BIGNUM_EQ_EXEC (1--3) THEN
    ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[WORD_OR_EQ_0] THEN
    ASM_REWRITE_TAC[GSYM VAL_EQ_0; WORD_RULE
     `word_sub (word (n + i)) (word n) = word i`] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [HIGHDIGITS_STEP] THEN
    REWRITE_TAC[ADD_EQ_0; MULT_EQ_0; EXP_EQ_0; ARITH_EQ] THEN
    REWRITE_TAC[GSYM ADD_ASSOC] THEN AP_TERM_TAC THEN
    REWRITE_TAC[VAL_EQ_0] THEN MATCH_MP_TAC WORD_EQ_0 THEN
    REWRITE_TAC[DIMINDEX_64; BIGDIGIT_BOUND]]);;

let BIGNUM_EQ_NOIBT_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_eq_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read RIP s' = returnaddress /\
                read RSP s' = word_add stackpointer (word 8) /\
                C_RETURN s' = if x = y then word 1 else word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  X86_PROMOTE_RETURN_NOSTACK_TAC bignum_eq_tmc BIGNUM_EQ_CORRECT);;

let BIGNUM_EQ_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_eq_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read RIP s' = returnaddress /\
                read RSP s' = word_add stackpointer (word 8) /\
                C_RETURN s' = if x = y then word 1 else word 0)
          (MAYCHANGE [RSP] ,, MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI)`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_EQ_NOIBT_SUBROUTINE_CORRECT));;

(* ------------------------------------------------------------------------- *)
(* Correctness of Windows ABI version.                                       *)
(* ------------------------------------------------------------------------- *)

let bignum_eq_windows_mc = define_from_elf
   "bignum_eq_windows_mc" "x86/generic/bignum_eq.obj";;

let bignum_eq_windows_tmc = define_trimmed "bignum_eq_windows_tmc" bignum_eq_windows_mc;;

let BIGNUM_EQ_NOIBT_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,LENGTH bignum_eq_windows_tmc); (a,8 * val m); (b,8 * val n)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_eq_windows_tmc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read RIP s' = returnaddress /\
                read RSP s' = word_add stackpointer (word 8) /\
                WINDOWS_C_RETURN s' = if x = y then word 1 else word 0)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  WINDOWS_X86_WRAP_NOSTACK_TAC bignum_eq_windows_tmc bignum_eq_tmc
    BIGNUM_EQ_CORRECT);;

let BIGNUM_EQ_WINDOWS_SUBROUTINE_CORRECT = prove
 (`!m a x n b y pc stackpointer returnaddress.
     ALL (nonoverlapping (word_sub stackpointer (word 16),16))
         [(word pc,LENGTH bignum_eq_windows_mc); (a,8 * val m); (b,8 * val n)]
     ==> ensures x86
          (\s. bytes_loaded s (word pc) bignum_eq_windows_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               WINDOWS_C_ARGUMENTS [m;a;n;b] s /\
               bignum_from_memory(a,val m) s = x /\
               bignum_from_memory(b,val n) s = y)
          (\s'. read RIP s' = returnaddress /\
                read RSP s' = word_add stackpointer (word 8) /\
                WINDOWS_C_RETURN s' = if x = y then word 1 else word 0)
          (MAYCHANGE [RSP] ,, WINDOWS_MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI ,,
          MAYCHANGE [memory :> bytes(word_sub stackpointer (word 16),16)])`,
  MATCH_ACCEPT_TAC(ADD_IBT_RULE BIGNUM_EQ_NOIBT_WINDOWS_SUBROUTINE_CORRECT));;



(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "x86/proofs/consttime.ml";;
needs "x86/proofs/subroutine_signatures.ml";;

let full_spec,public_vars = mk_safety_spec
    (assoc "bignum_eq" subroutine_signatures)
    BIGNUM_EQ_CORRECT
    BIGNUM_EQ_EXEC;;

let allowed_vars_e = ref [];;

let RUN_AND_FINALIZE_TAC exec nsteps =
  ENSURES_INIT_TAC "s0" THEN
  (* break any 'exists e2. ..' *)
  TRY (FIRST_X_ASSUM (STRIP_ASSUME_TAC o (check (is_exists o concl)))) THEN
  X86_STEPS_TAC BIGNUM_EQ_EXEC (1--nsteps) THEN
  ENSURES_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[];;

let EXISTS_E2_TAC allowed_vars_e =
  CONV_TAC (TRY_CONV (LAND_CONV CONS_TO_APPEND_CONV)) THEN
  REWRITE_TAC[APPEND_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  SAFE_UNIFY_REFL_TAC allowed_vars_e;;



extra_word_CONV := [GEN_REWRITE_CONV I
  [WORD_BLAST `word (8 * (x + 1) + 18446744073709551608):int64 =
               word (8 * x)`]] @ !extra_word_CONV;;

let BIGNUM_EQ_SAFE = time prove
 (`exists f_events.
       forall e m a n b pc.
           ensures x86
           (\s.
                bytes_loaded s (word pc) (BUTLAST bignum_eq_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [m; a; n; b] s /\
                read events s = e)
           (\s.
                exists e2.
                    read RIP s = word (pc + 66) /\
                    read events s = APPEND e2 e /\
                    e2 = f_events a b n m pc /\
                    memaccess_inbounds e2 [a,val m * 8; b,val n * 8] [])
           (\s s'. true)`,

  (* Explicitly give the structure of the event trace. *)
  SUBGOAL_THEN `
    exists
        // Basic blocks entry ~ mtest
        f_ev_eq f_ev_ne_nm f_ev_nm_loop
        f_ev_ne_mn f_ev_mn_loop f_ev_ne_mn_post
        // Basic blocks mmain ~ end
        f_ev_end f_ev_mmain f_ev_loop.
       forall e m a n b pc.
           ensures x86
           (\s.
                bytes_loaded s (word pc) (BUTLAST bignum_eq_tmc) /\
                read RIP s = word pc /\
                C_ARGUMENTS [m; a; n; b] s /\
                read events s = e)
           (\s.
                exists e2.
                  read RIP s = word (pc + 66) /\
                  read events s = APPEND e2 e /\
                  e2 = APPEND
                    // From BB mmain ~ end
                    (if (MIN (val m) (val n) = 0)
                      then f_ev_end a b n m pc
                      else
                        (APPEND
                          (ENUMERATEL (MIN (val m) (val n)) (f_ev_loop a b n m pc))
                          (f_ev_mmain a b n m pc)))
                    // From the entry ~ mtest
                    (if val m = val n then
                        f_ev_eq a b n m pc
                      else if val m < val n then
                        APPEND
                          (APPEND
                            (f_ev_ne_mn_post a b n m pc)
                            (ENUMERATEL (val n - val m:num) (f_ev_mn_loop a b n m pc)))
                          (f_ev_ne_mn a b n m pc)
                      else
                        APPEND
                          (ENUMERATEL (val m - val n:num) (f_ev_nm_loop a b n m pc))
                          (f_ev_ne_nm a b n m pc)) /\
                  memaccess_inbounds e2 [a,val m * 8; b,val n * 8] [])
           (\s s'. true)` MP_TAC THENL [
    ALL_TAC;

    STRIP_TAC THEN
    (fun (asl,w) ->
      let asm_of_interest = concl (snd (hd asl)) in
      let ts = snd (strip_forall asm_of_interest) in
      let _,(_::_::postcond::_) = strip_comb ts in
      let body = snd (dest_abs postcond) in
      let body = snd (dest_exists body) in
      let _::_::e2_def::_ = conjuncts body in
      let answ =
          list_mk_abs ([`a:int64`;`b:int64`;`n:int64`;`m:int64`;`pc:num`],
            (rhs e2_def)) in
      let _ = Printf.printf "%s\n" (string_of_term answ) in
      EXISTS_TAC answ (asl,w)) THEN
    ASM_REWRITE_TAC[]
  ] THEN

  REPEAT META_EXISTS_TAC THEN
  STRIP_TAC (* event e *) THEN

  W64_GEN_TAC `m:num` THEN X_GEN_TAC `a:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `b:int64` THEN
  X_GEN_TAC `pc:num` THEN
  REWRITE_TAC[C_ARGUMENTS; fst BIGNUM_EQ_EXEC] THEN

  (*** Split into subgoals at "mmain" label and do the second part first ***)

  ABBREV_TAC `p = MIN m n` THEN VAL_INT64_TAC `p:num` THEN

  ENSURES_SEQUENCE_TAC `pc + 0x22`
   `\s. read RDI s = word p /\
        read RSI s = a /\
        read RCX s = b /\
        exists e2.
          (read events s = APPEND e2 e /\
           e2 =
            (if m = n then
              f_ev_eq a b (word n:int64) (word m:int64) (pc:num)
             else if m < n then
              APPEND
                (APPEND
                  (f_ev_ne_mn_post a b (word n:int64) (word m:int64) pc)
                  (ENUMERATEL (n - m:num) (f_ev_mn_loop a b (word n:int64) (word m:int64) pc)))
                (f_ev_ne_mn a b (word n:int64) (word m:int64) pc)
             else
              APPEND
                (ENUMERATEL (m - n:num) (f_ev_nm_loop a b (word n:int64) (word m:int64) pc))
                (f_ev_ne_nm a b (word n:int64) (word m:int64) pc)) /\
           memaccess_inbounds e2 [a,m*8; b,n*8] [])` THEN
  CONJ_TAC THENL
   [ALL_TAC;

    ASM_CASES_TAC `p = 0` THENL
     [RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 5 THEN

      SAFE_META_EXISTS_TAC allowed_vars_e THEN
      CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC] THEN
      CONJ_TAC THENL [
        AP_THM_TAC THEN AP_TERM_TAC THEN
        (* todo: this must be a tactic. *)
        ABBREV_TAC `wn = (word n:int64)` THEN
        ABBREV_TAC `wm = (word m:int64)` THEN
        SAFE_UNIFY_REFL_TAC (ref []);

        ALL_TAC] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC;

      ALL_TAC] THEN

    ASM_REWRITE_TAC[] THEN
    ENSURES_WHILE_DOWN2_TAC `p:num` `pc + 0x27`
     `pc + 0x39` (* not 0x37; look at the description of the tactic *)
     `\i s. read RDI s = word i /\
            read RSI s = a /\
            read RCX s = b /\
            exists e2.
             (read events s = APPEND e2 e /\
              e2 = APPEND
                  (APPEND
                    (ENUMERATEL (p - i) (f_ev_loop a b (word n:int64) (word m:int64) (pc:num)))
                    (f_ev_mmain a b (word n:int64) (word m:int64) (pc:num)))
                  (if m = n then
                    f_ev_eq a b (word n:int64) (word m:int64) pc
                   else if m < n then
                    APPEND
                      (APPEND
                        (f_ev_ne_mn_post a b (word n:int64) (word m:int64) pc)
                        (ENUMERATEL (n - m:num) (f_ev_mn_loop a b (word n:int64) (word m:int64) pc)))
                      (f_ev_ne_mn a b (word n:int64) (word m:int64) pc)
                   else
                     APPEND
                      (ENUMERATEL (m - n:num) (f_ev_nm_loop a b (word n:int64) (word m:int64) pc))
                      (f_ev_ne_nm a b (word n:int64) (word m:int64) pc)) /\
              memaccess_inbounds e2 [a,m*8; b,n*8] [])` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 2 THEN
      (* fill in e2 *)
      SAFE_META_EXISTS_TAC allowed_vars_e THEN
      CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
      CONJ_TAC THENL [
        (* f_ev_mmain *)
        REWRITE_TAC[ENUMERATEL_APPEND_ZERO] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN
        (* todo: this must be a tactic. *)
        ABBREV_TAC `wn = (word n:int64)` THEN
        ABBREV_TAC `wm = (word m:int64)` THEN
        SAFE_UNIFY_REFL_TAC (ref []);

        ALL_TAC
      ] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC;

      ALL_TAC; (*** Main loop invariant ***)

      (* to postcond *)
      REWRITE_TAC[SUB_0] THEN
      RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 3 THEN
      (* fill in e2 *)
      SAFE_META_EXISTS_TAC allowed_vars_e THEN
      CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
      CONJ_TAC THENL [
        (* nothing here. *)
        REFL_TAC;

        ALL_TAC
      ] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC] THEN

    (* The main loop *)
    (* do r 1;; before here. this is a bug in vscode plugin. *)
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i:num < m /\ i < n` STRIP_ASSUME_TAC THENL
     [SIMPLE_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `i + 1`] THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (i + 1)) (word 1):int64 = word i`) THEN

    RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 5 THEN
    (* PC *)
    CONJ_TAC THENL [
      REWRITE_TAC[ARITH_RULE`(i > 0) <=> ~(i = 0)`] THEN
      ARITH_TAC; ALL_TAC
    ] THEN
    (* fill in e2 *)
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [
      (* f_ev_loop *)
      AP_THM_TAC THEN AP_TERM_TAC THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      (* ENUMERATEL *)
      ASM_SIMP_TAC[ARITH_RULE`i < p ==> p - i = (p - (i + 1)) + 1`] THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      (* abbreviate all parameters of f_ev_loop. *)
      ABBREV_TAC `wn = (word n:int64)` THEN
      SUBGOAL_THEN `n = val (wn:int64)` SUBST_ALL_TAC THENL
      [ ASM_SIMP_TAC[WORD_VAL]; ALL_TAC ] THEN
      ABBREV_TAC `wm = (word m:int64)` THEN
      SUBGOAL_THEN `m = val (wm:int64)` SUBST_ALL_TAC THENL
      [ ASM_SIMP_TAC[WORD_VAL]; ALL_TAC ] THEN
      ABBREV_TAC `i' = p - (i + 1)` THEN
      SUBGOAL_THEN `i = p - i' - 1` SUBST_ALL_TAC THENL [
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      SUBST_ALL_TAC (GSYM (ASSUME `MIN (val (wm:int64)) (val (wn:int64)) = p`)) THEN
      SAFE_UNIFY_REFL_TAC (ref []);

      ALL_TAC
    ] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC
   ] THEN

  (*** The case m = n, which is a simple drop-through ***)

  ASM_CASES_TAC `m:num = n` THENL
   [UNDISCH_THEN `m:num = n` SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (ARITH_RULE
     `MIN n n = p ==> p = n`)) THEN
    RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 4 THEN
    (* fill in e2 *)
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [
      (* f_ev_eq. *)
      ABBREV_TAC `wn = (word n:int64)` THEN
      ABBREV_TAC `wm = (word m:int64)` THEN
      SAFE_UNIFY_REFL_TAC (ref []);

      ALL_TAC
    ] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC;
    ALL_TAC] THEN

  (*** Now the n > m and m > n cases respectively, very similar proofs ***)

  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `~(m:num = n) ==> m < n \/ n < m`)) THEN
  UNDISCH_TAC `MIN m n = p` THEN
  ASM_SIMP_TAC[ARITH_RULE `m < n ==> MIN m n = m`;
               ARITH_RULE `n < m ==> MIN m n = n`;
               LT_IMP_NE; ARITH_RULE `n < m ==> ~(m < n)`] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THENL
   [ENSURES_WHILE_DOWN2_TAC `n - m:num` `pc + 0x8`
     `pc + 0x14` (* not pc + 0x12 because ENSURES_WHILE_DOWN2_TAC receives the
                    PC after backedge is untaken *)
     `\i s. read RDI s = word m /\
            read RSI s = a /\
            read RDX s = word(m + i) /\
            read RCX s = b /\
            exists e2.
              read events s = APPEND e2 e /\
              e2 = APPEND
                (ENUMERATEL (n - m - i)
                    (f_ev_mn_loop a b (word n:int64) (word m:int64) (pc:num)))
                (f_ev_ne_mn a b (word n:int64) (word m:int64) pc) /\
              memaccess_inbounds e2 [a,m*8; b,n*8] []` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `m:num < n` THEN ARITH_TAC;

      (* precond *)
      RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 3 THEN
      (* pc *)
      CONJ_TAC THENL [
        ASM_SIMP_TAC[GSYM LT_IMP_NE; ARITH_RULE `m:num < n ==> m + n - m = n`];
        ALL_TAC
      ] THEN
      (* fill in e2 *)
      SAFE_META_EXISTS_TAC allowed_vars_e THEN
      CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
      CONJ_TAC THENL [
        (* f_ev_ne_mn. *)
        ASM_SIMP_TAC[ENUMERATEL_APPEND_ZERO] THEN
        ABBREV_TAC `wn = (word n:int64)` THEN
        ABBREV_TAC `wm = (word m:int64)` THEN
        SAFE_UNIFY_REFL_TAC (ref []);

        ALL_TAC
      ] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC;

      ALL_TAC; (*** Main loop invariant ***)

      (* postcond *)
      RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 1 THEN
      (* fill in e2 *)
      SAFE_META_EXISTS_TAC allowed_vars_e THEN
      CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
      CONJ_TAC THENL [
        (* f_ev_ne_mn_post *)
        ASM_SIMP_TAC[SUB_0; ARITH_RULE`m < n ==> ~(m = n)`] THEN
        REWRITE_TAC[APPEND_ASSOC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ABBREV_TAC `wn = (word n:int64)` THEN
        ABBREV_TAC `wm = (word m:int64)` THEN
        SAFE_UNIFY_REFL_TAC (ref []);

        ALL_TAC
      ] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC
     ] THEN

    (* main loop *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (m + i + 1)) (word 1):int64 = word(m + i)`) THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `m + i:num`] THEN
    RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 4 THEN
    (* the branch condition *)
    CONJ_TAC THENL [
      REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0;
        WORD_RULE `word_sub (word m) (word (m + i)) = word_neg(word i)`] THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
      ARITH_TAC;
      ALL_TAC
    ] THEN

    (* fill in e2 *)
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [
      (* f_ev_mn_loop *)
      ASM_SIMP_TAC[ARITH_RULE`i < n - m ==> n - m - i = (n - m - (i + 1)) + 1`] THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN
      REWRITE_TAC[APPEND_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      (* abbreviate all parameters of f_ev_mn_loop. *)
      ABBREV_TAC `i' = n - m - (i + 1)` THEN
      SUBGOAL_THEN `i = n - m - i' - 1` SUBST_ALL_TAC THENL [
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      ABBREV_TAC `wn = (word n:int64)` THEN
      SUBGOAL_THEN `n = val (wn:int64)` SUBST_ALL_TAC THENL
      [ ASM_SIMP_TAC[WORD_VAL]; ALL_TAC ] THEN
      ABBREV_TAC `wm = (word m:int64)` THEN
      SUBGOAL_THEN `m = val (wm:int64)` SUBST_ALL_TAC THENL
      [ ASM_SIMP_TAC[WORD_VAL]; ALL_TAC ] THEN
      SAFE_UNIFY_REFL_TAC (ref []);

      ALL_TAC
    ] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC;


    ENSURES_WHILE_DOWN2_TAC `m - n:num` `pc + 0x16` `pc + 0x22`
     `\i s. read RDI s = word(n + i) /\
            read RSI s = a /\
            read RDX s = word n /\
            read RCX s = b /\
            exists e2.
              read events s = APPEND e2 e /\
              e2 = APPEND
                (ENUMERATEL (m - n - i)
                    (f_ev_nm_loop a b (word n:int64) (word m:int64) (pc:num)))
                (f_ev_ne_nm a b (word n:int64) (word m:int64) pc) /\
              memaccess_inbounds e2 [a,m*8; b,n*8] []` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `n:num < m` THEN ARITH_TAC;

      (* precond *)
      SUBGOAL_THEN `n <= m` ASSUME_TAC THENL [SIMPLE_ARITH_TAC;ALL_TAC] THEN
      RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 4 THEN
      ASM_SIMP_TAC[ARITH_RULE `m:num < n ==> m + n - m = n`] THEN
      (* PC *)
      CONJ_TAC THENL [
        ASM_SIMP_TAC[VAL_WORD_SUB_CASES] THEN
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      (* fill in e2 *)
      SAFE_META_EXISTS_TAC allowed_vars_e THEN
      CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
      CONJ_TAC THENL [
        (* f_ev_ne_nm. *)
        ASM_SIMP_TAC[ENUMERATEL_APPEND_ZERO] THEN
        ABBREV_TAC `wn = (word n:int64)` THEN
        ABBREV_TAC `wm = (word m:int64)` THEN
        SAFE_UNIFY_REFL_TAC (ref []);

        ALL_TAC
      ] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC;

      ALL_TAC; (*** Main loop invariant ***)

      (* postcond *)
      REWRITE_TAC[SUB_0] THEN
      ENSURES_INIT_TAC "s0" THEN
      (* break 'exists e2' *)
      FIRST_X_ASSUM (STRIP_ASSUME_TAC o (check (is_exists o concl))) THEN
      ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
      (* pc *)
      CONJ_TAC THENL [REWRITE_TAC[ADD_0] THEN NO_TAC; ALL_TAC] THEN
      (* fill in e2 *)
      SAFE_META_EXISTS_TAC allowed_vars_e THEN
      CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
      CONJ_TAC THENL [
        (* f_ev_ne_nm_post *)
        ASM_SIMP_TAC[SUB_0; ARITH_RULE`m < n ==> ~(m = n)`] THEN
        REWRITE_TAC[APPEND_ASSOC] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ABBREV_TAC `wn = (word n:int64)` THEN
        ABBREV_TAC `wm = (word m:int64)` THEN
        SAFE_UNIFY_REFL_TAC (ref []);

        ALL_TAC
      ] THEN
      DISCHARGE_MEMACCESS_INBOUNDS_TAC
     ] THEN

    (* main loop *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASSUME_TAC(WORD_RULE
     `word_sub (word (n + i + 1)) (word 1):int64 = word(n + i)`) THEN
    MAP_EVERY VAL_INT64_TAC [`i:num`; `n + i:num`] THEN
    RUN_AND_FINALIZE_TAC BIGNUM_EQ_EXEC 4 THEN
    (* the branch condition *)
    CONJ_TAC THENL [
      REWRITE_TAC[VAL_EQ_0; WORD_NEG_EQ_0;
        WORD_RULE `word_sub (word (n + i)) (word n) = word i`] THEN
      ASM_REWRITE_TAC[GSYM VAL_EQ_0] THEN
      ARITH_TAC;
      ALL_TAC
    ] THEN

    (* fill in e2 *)
    SAFE_META_EXISTS_TAC allowed_vars_e THEN
    CONJ_TAC THENL [ EXISTS_E2_TAC allowed_vars_e; ALL_TAC ] THEN
    CONJ_TAC THENL [
      (* f_ev_mn_loop *)
      ASM_SIMP_TAC[ARITH_RULE`i < m - n ==> m - n - i = (m - n - (i + 1)) + 1`] THEN
      REWRITE_TAC[ENUMERATEL_ADD1] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      (* abbreviate all parameters of f_ev_mn_loop. *)
      (* todo: this must be a tactic. *)
      ABBREV_TAC `i' = m - n - (i + 1)` THEN
      SUBGOAL_THEN `i = m - n - i' - 1` SUBST_ALL_TAC THENL [
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      ABBREV_TAC `wn = (word n:int64)` THEN
      SUBGOAL_THEN `n = val (wn:int64)` SUBST_ALL_TAC THENL
      [ ASM_SIMP_TAC[WORD_VAL]; ALL_TAC ] THEN
      ABBREV_TAC `wm = (word m:int64)` THEN
      SUBGOAL_THEN `m = val (wm:int64)` SUBST_ALL_TAC THENL
      [ ASM_SIMP_TAC[WORD_VAL]; ALL_TAC ] THEN
      SAFE_UNIFY_REFL_TAC (ref []);

      ALL_TAC
    ] THEN
    DISCHARGE_MEMACCESS_INBOUNDS_TAC
  ]
 );;
