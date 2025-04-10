(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Lemmas and tactics for constant-time proofs                               *)
(* ========================================================================= *)

needs "common/relational_n.ml";;

(* ------------------------------------------------------------------------- *)
(* Definitions and lemmas for the event trace.                               *)
(* ------------------------------------------------------------------------- *)

let ENUMERATEL = new_recursive_definition num_RECURSION
  `(ENUMERATEL 0 (f:num->A list) = []) /\
   (ENUMERATEL (SUC n) f = APPEND (f n) (ENUMERATEL n f))`;;

let ENUMERATEL_ADD1 = prove(
  `forall n f:num->A list. ENUMERATEL (n + 1) f = APPEND (f n) (ENUMERATEL n f)`,
  REWRITE_TAC [GSYM ADD1; ENUMERATEL]);;


(* ------------------------------------------------------------------------- *)
(* Get ranges of bignum abbreviation out of precondition.                    *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_BIGNUM_RANGE_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND])
  and nty = `:num` in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th -> REWRITE_TAC[th; ENSURES_N_TRIVIAL] THEN NO_TAC)
     (SPECL [mk_var(k,nty); mk_var(m,nty)] pth);;

let ENSURES_N_BIGNUM_TERMRANGE_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND]) in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th -> REWRITE_TAC[th; ENSURES_N_TRIVIAL] THEN NO_TAC)
     (SPECL [k; m] pth);;


let ARM_N_SIM_TAC execth stnames ?(rewrite_read_pc=false) =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_N_INIT_TAC "s0" THEN
  (if rewrite_read_pc then
    FIRST_X_ASSUM (fun th ->
      if (can (term_match [] `read PC s`) (lhs (concl th)))
      then RULE_ASSUM_TAC (REWRITE_RULE[th]) THEN ASSUME_TAC th
      else NO_TAC)
  else ALL_TAC) THEN
  ARM_N_STEPS_TAC execth stnames "" [] None THEN
  ENSURES_N_FINAL_STATE_TAC THEN
  ASM_REWRITE_TAC[];;


let DROP_EVENTS_COND = prove(
  `!P Q C fn. (?es'. !es. ensures_n arm (\s. P s /\ read events s = es)
                                        (\s. Q s /\ read events s = APPEND es' es) C fn) ==>
    ensures_n arm (\s. P s) (\s. Q s) C fn`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!es. ensures_n arm (\s. P s /\ read events s = es) (\s. Q s) C fn` ASSUME_TAC THENL [
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC ENSURES_N_POSTCONDITION_THM THEN
    META_EXISTS_TAC THEN ONCE_REWRITE_TAC [TAUT `!P Q. P /\ Q <=> Q /\ P`] THEN
    CONJ_TAC THENL [
      FIRST_X_ASSUM (MP_TAC o SPEC_ALL) THEN
      DISCH_THEN (UNIFY_ACCEPT_TAC [`Q':armstate->bool`]);
      MESON_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV) [MESON[] `P s <=> P s /\ ?es. read events s = es`] THEN
  ASM_MESON_TAC[ensures_n]);;

let DROP_EVENTS_COND_TAC th =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC DROP_EVENTS_COND THEN
  CHOOSE_THEN (MP_TAC o GEN `es:armevent list` o SPEC_ALL) th THEN
  ASM_REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN (fun th ->
    META_EXISTS_TAC THEN UNIFY_ACCEPT_TAC [`es':armevent list`] th);;

let ARM_N_ADD_RETURN_NOSTACK_TAC =
  let lemma1 = prove
   (`ensures_n step P Q R fn /\
     (!s s'. P s /\ Q s' /\ R s s' ==> Q' s')
     ==> ensures_n step P (\s. Q s /\ Q' s) R fn`,
    ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_N_SUBLEMMA_THM THEN
    REWRITE_TAC[SUBSUMED_REFL] THEN ASM_MESON_TAC[]) in
  let ENSURES_N_TRANS_SUBSUMED = prove(`!P Q R C C' n1 n2.
        C ,, C = C /\ C subsumed C' /\
        ensures_n step P Q C (\s. n1) /\ ensures_n step Q R C (\s. n2)
        ==> ensures_n step P R C' (\s. n1 + n2)`,
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[ENSURES_N_TRANS_SIMPLE; ENSURES_N_FRAME_SUBSUMED]) in
  let lemma2 = prove
   (`C ,, C = C /\ C subsumed C' /\
     (!s s'. program_decodes s /\ pcdata s /\ returndata s /\ P s /\
             Q s' /\ C s s'
             ==> program_decodes s' /\ returndata s') /\
     ensures_n step (\s. program_decodes s /\ returndata s /\ Q s) R C (\s. 1)
     ==> ensures_n step (\s. program_decodes s /\ pcdata s /\ P s) Q C (\s. n)
          ==> ensures_n step
               (\s. program_decodes s /\ pcdata s /\ returndata s /\ P s) R C' (\s. n + 1)`,
    ONCE_REWRITE_TAC[TAUT
     `a /\ p /\ subsm /\ q ==> r ==> s <=>
      a ==> p ==> subsm ==> r ==> q ==> s`] THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE
     [TAUT `p /\ q /\ r /\ r2 ==> s <=> p /\ q /\ r ==> r2 ==> s`]
     ENSURES_N_TRANS_SUBSUMED) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o BINDER_CONV)
     [TAUT `p /\ q /\ r <=> r /\ p /\ q`] THEN
    MATCH_MP_TAC lemma1 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          ENSURES_N_PRECONDITION_THM)) THEN
    SIMP_TAC[]) in
  fun execth coreth ->
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MP_TAC coreth THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN ALIGNED_16_TAC THEN
      TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    MATCH_MP_TAC lemma2 THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC;
      SUBSUMED_MAYCHANGE_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      NONSELFMODIFYING_STATE_UPDATE_TAC
       (MATCH_MP aligned_bytes_loaded_update (fst execth)) THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN
      DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_N_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check
       (can (term_match [] `read PC s = a \/ Q` o concl)))) THEN
      ARM_N_STEPS_TAC execth [1] "" [] None THEN
      ENSURES_N_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[]];;
