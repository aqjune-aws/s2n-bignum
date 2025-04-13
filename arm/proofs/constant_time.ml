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


(* ------------------------------------------------------------------------- *)
(* ensures_n version of ARM symbolic simulation tactics                      *)
(* ------------------------------------------------------------------------- *)

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


let ARM_N_VERBOSE_STEP_TAC (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  ARM_N_STEP_TAC (exth1,exth2) [] sname None g;;

let ARM_N_SINGLE_STEP_TAC th s =
  time (ARM_N_VERBOSE_STEP_TAC th s None) THEN
  DISCARD_OLDSTATE_TAC s THEN
  CLARIFY_TAC;;

let ARM_N_GEN_ACCSTEP_TAC acc_preproc th aflag s =
  ARM_N_SINGLE_STEP_TAC th s THEN
  (if aflag then acc_preproc THEN TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
   else ALL_TAC);;

let ARM_N_GEN_ACCSTEPS_TAC acc_preproc th anums snums =
  MAP_EVERY
    (fun n ->
      let state_name = "s"^string_of_int n in
      ARM_N_GEN_ACCSTEP_TAC (acc_preproc state_name) th (mem n anums) state_name)
    snums;;

let ARM_N_ACCSTEPS_TAC th anums snums =
  ARM_N_GEN_ACCSTEPS_TAC (fun _ -> ALL_TAC) th anums snums;;

let ARM_N_QUICKSTEP_TAC th pats =
  let pats' =
   [`nonoverlapping_modulo a b c`; `aligned_bytes_loaded a b c`;
    `MAYCHANGE a b c`; `(a ,, b) c d`; `read PC s = x`; `steps arm i s0 si`] @ pats in
  fun s -> time (ARM_N_VERBOSE_STEP_TAC th s None) THEN
           DISCARD_NONMATCHING_ASSUMPTIONS pats' THEN
           DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC;;

let ARM_N_QUICKSTEPS_TAC th pats snums =
  MAP_EVERY (ARM_N_QUICKSTEP_TAC th pats) (statenames "s" snums);;

let ARM_N_QUICKSIM_TAC execth pats snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_N_INIT_TAC "s0" THEN ARM_N_QUICKSTEPS_TAC execth pats snums THEN
  ENSURES_N_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Introduce a new ghost variable for a state component in "ensures_n".      *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_GHOST_INTRO_TAC =
  let pth = prove
   (`!f P step post frame fn.
         (!a. ensures_n step (\s. P s a /\ f s = a) post frame fn)
         ==> ensures_n step (\s. P s (f s)) post frame fn`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ_ALT; FORALL_UNWIND_THM1]) in
  fun t comp ->
    MP_TAC(ISPEC comp pth) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BETA_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC t THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV o TOP_DEPTH_CONV)
     [GSYM CONJ_ASSOC];;

(* ------------------------------------------------------------------------- *)
(* Simulate through a lemma in ?- ensures_n step P Q C ==> eventually_n R s  *)
(* ------------------------------------------------------------------------- *)

let (ARM_N_BIGSTEP_TAC:(thm*thm option array)->string->tactic) =
  let lemma = prove
   (`P s /\ (!s':S. Q s' /\ C s s' ==> eventually_n step n2 R s')
     ==> ensures_n step P Q C (\s. n1) ==> eventually_n step (n1 + n2) R s`,
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ensures_n] THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `(!s:S n1. eventually_n step n1 P s ==> eventually_n step (n1 + n2) Q s)
      ==> eventually_n step n1 P s ==> eventually_n step (n1 + n2) Q s`) THEN
    GEN_REWRITE_TAC I [EVENTUALLY_N_IMP_EVENTUALLY_N] THEN
    ASM_REWRITE_TAC[]) in
  fun (execth1,_) sname (asl,w) ->
    let sv = mk_var(sname,type_of(rand(rand w))) in
    (GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
      (!simulation_precanon_thms) THEN
     MATCH_MP_TAC lemma THEN CONJ_TAC THENL
      [BETA_TAC THEN ASM_REWRITE_TAC[];
       BETA_TAC THEN X_GEN_TAC sv THEN
       REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       NONSELFMODIFYING_STATE_UPDATE_TAC
        (MATCH_MP aligned_bytes_loaded_update execth1) THEN
       ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN DISCARD_OLDSTATE_TAC sname])
    (asl,w);;