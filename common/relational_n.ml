(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*     Hoare Logic with the number of small steps explicitly annotated.      *)
(*                                                                           *)
(*                         Abdalrhman M Mohamed (2024)                       *)
(*                                Juneyoung Lee                              *)
(* ========================================================================= *)

needs "common/bignum.ml";;
needs "common/components.ml";;
needs "common/relational.ml";;

(* ------------------------------------------------------------------------- *)
(* A definition of steps and its properties.                                 *)
(* ------------------------------------------------------------------------- *)

let steps_RULES,steps_INDUCT,steps_CASES = new_inductive_definition
  `(!s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (!s s'' n. (?s'. step s s' /\ steps step n s' s'') ==> steps step (n+1) s s'')`;;

let STEPS_TRIVIAL = prove(
  `!(s:S) s' step. steps step 0 s s' <=> s = s'`,
  ONCE_REWRITE_TAC[steps_CASES] THEN REWRITE_TAC[ARITH_RULE`~(0=n+1)`] THEN MESON_TAC[]);;

(* Trivial, but to help pattern matcher... *)
let STEPS_SYM = prove(
  `!(step:S->S->bool) m n s s'. steps step (m+n) s s' <=> steps step (n+m) s s'`,
  REWRITE_TAC[ADD_SYM]);;

let STEPS_STEP_LEFT_RIGHT = prove(
  `!(step:S->S->bool) n s s'.
      (?s''. step s s'' /\ steps step n s'' s') <=> (?s''. steps step n s s'' /\ step s'' s')`,
  GEN_TAC THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
    MESON_TAC[STEPS_TRIVIAL];

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE`SUC n=1+n`] THEN
    ONCE_REWRITE_TAC [steps_CASES] THEN
    REWRITE_TAC[ARITH_RULE`~(1+n = 0)`] THEN
    SUBGOAL_THEN `!k (P:num->bool). (?n'. 1+k = n'+1 /\ P n') <=> P k`
        (fun th -> REWRITE_TAC[th]) THENL [
      REPEAT GEN_TAC THEN EQ_TAC THENL [
        REPEAT STRIP_TAC THEN
        SUBGOAL_THEN `k:num=n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[ADD_SYM];

        REPEAT STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[ADD_SYM]
      ];
      ALL_TAC
    ] THEN
    let tt1 = `!P Q. (?a. P a /\ (?b. Q a b)) <=> (?a b. P a /\ Q a b)` in
    let tt2 = `!P Q. (?a. (?b. Q a b) /\ P a) <=> (?a b. Q a b /\ P a)` in
    REWRITE_TAC(map ITAUT [tt1;tt2]) THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    let tt3 = `!P Q. (?b a. P a /\ Q a b) <=> (?a. P a /\ (?b. Q a b))` in
    REWRITE_TAC[ITAUT tt3] THEN
    ASM_MESON_TAC[]
  ]);;

let STEPS_ADD =
  let lemma = prove(`!k (P:num->bool). (?n'. k+1 = n'+1 /\ P n') <=> P k`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `k:num=n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];

    REPEAT STRIP_TAC THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]
  ]) in
  prove(
    `!(step:S->S->bool) m n s s'.
    steps step (m+n) s s' <=> ?s''. steps step m s s'' /\ steps step n s'' s'`,
    REPEAT_N 2 GEN_TAC THEN
    MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
      REWRITE_TAC[ADD_0;STEPS_TRIVIAL] THEN MESON_TAC[];

      REWRITE_TAC[ARITH_RULE`m + SUC n = (m + n) + 1`;ARITH_RULE`SUC n = n + 1`] THEN
      REPEAT STRIP_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
      ASM_REWRITE_TAC[ARITH_RULE`!m n. ~((m+n)+1 = 0)`;lemma] THEN
      SUBGOAL_THEN `!(s'':S).
          (steps (step:S->S->bool) (n + 1) s'' s' <=>
          ?s'''. step s'' s''' /\ steps step n s''' s')`
          (fun th -> REWRITE_TAC[th]) THENL [
        REPEAT STRIP_TAC THEN
        GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
        REWRITE_TAC[ARITH_RULE`!n. ~(n+1=0)`;lemma];
        ALL_TAC
      ] THEN
      REWRITE_TAC[CONJ_ASSOC;
        ITAUT `!P Q. (?a. P a /\ (?b. Q a b)) <=> (?a b. P a /\ Q a b)`;
        ITAUT `!P Q. (?a b. P a b /\ Q b) <=> (?b. (?a. P a b) /\ Q b)`] THEN
      REWRITE_TAC[STEPS_STEP_LEFT_RIGHT]
    ]);;

(* Again trivial, but for pattern matching... *)
let STEPS_STEP = prove(
  `!n (s:S) s' step.
     steps step (1+n) s s' <=> ?s''. step s s'' /\ steps step n s'' s'`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [steps_CASES] THEN
  REWRITE_TAC[ARITH_RULE`~(1+n=0)`] THEN
  EQ_TAC THENL [
    STRIP_TAC THEN
    SUBGOAL_THEN `n:num = n'` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[];

    STRIP_TAC THEN
    EXISTS_TAC `n:num` THEN
    REWRITE_TAC[ADD_SYM] THEN ASM_MESON_TAC[]]);;

let STEPS_ONE = prove(
  `!(s:S) s' step. steps step 1 s s' <=> step s s'`,
  METIS_TAC[ARITH_RULE`1=1+0`;STEPS_STEP;STEPS_TRIVIAL]);;

let STEPS_NOSTUCK = prove(
  `!(step:S->S->bool) (n:num) (s:S).
    (!s' n'. (n' < n /\ steps step n' s s') ==> ?s''. step s' s'')
    ==> ?s'. steps step n s s'`,
  GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
    MESON_TAC[STEPS_TRIVIAL];

    REPEAT STRIP_TAC THEN
    REWRITE_TAC[ARITH_RULE`SUC n=1+n`;STEPS_STEP;STEPS_STEP_LEFT_RIGHT] THEN
    SUBGOAL_THEN
        `(!(s':S) n'. (n' < n /\ steps (step:S->S->bool) n' s s' ==> (?s''. step s' s''))) /\
        (!(s':S). steps (step:S->S->bool) n s s' ==> (?s''. step s' s''))`
        MP_TAC THENL [
      CONJ_TAC THENL [
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC`n':num` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;

        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC`n:num` THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC
      ];
      ALL_TAC
    ] THEN
    DISCH_THEN (fun th -> let th1,th2 = CONJ_PAIR th in
      LABEL_TAC "H1" th1 THEN LABEL_TAC "H2" th2) THEN
    SUBGOAL_THEN `?(s':S). steps step n s s'` MP_TAC THENL [
      ASM_MESON_TAC[]; ALL_TAC
    ] THEN STRIP_TAC THEN
    ASM_MESON_TAC[]
  ]);;


(* ------------------------------------------------------------------------- *)
(* A definition of eventually with # steps.                                  *)
(* ------------------------------------------------------------------------- *)

let eventually_n = new_definition
  `eventually_n (step:S->S->bool) (n:num) (P:S->bool) s <=>
   ((!s'. steps step n s s' ==> P s') /\
    // There isn't a 'stuck' state at the end of a trace shorter than n
    (!s' n'. (n' < n /\ steps step n' s s') ==> ?s''. step s' s''))`;;


(* ------------------------------------------------------------------------- *)
(* Properties of eventually_n                                                *)
(* ------------------------------------------------------------------------- *)

let EVENTUALLY_N_TRIVIAL = prove(
  `!(step:S->S->bool) s (P:S->bool). eventually_n step 0 P s <=> P s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually_n;ARITH_RULE`!x. ~(x<0)`] THEN
  MESON_TAC[STEPS_TRIVIAL]);;

let EVENTUALLY_N_CONJ = prove(
  `!(step:S->S->bool) (P:S->bool) (Q:S->bool) n s.
    eventually_n step n P s /\ eventually_n step n Q s ==>
    eventually_n step n (\s. P s /\ Q s) s`,
  REWRITE_TAC[eventually_n] THEN MESON_TAC[]);;

let EVENTUALLY_N_NESTED = prove(
  `!(step:S->S->bool) (s0:S).
    eventually_n step n (\s. eventually_n step n (\s2. P s s2) s0) s0 ==>
    eventually_n step n (\s. P s s) s0`,
  REWRITE_TAC[eventually_n] THEN
  REPEAT STRIP_TAC THENL
  replicate (ASM_MESON_TAC[]) 2);;

let EVENTUALLY_N_COMPOSE = prove(
  `forall (step:S->S->bool) (s0:S) n1 n2 P Q.
    eventually_n step n1 P s0 /\
    (forall s. P s ==> eventually_n step n2 Q s)
    ==> eventually_n step (n1+n2) Q s0`,
  REWRITE_TAC[eventually_n] THEN REPEAT GEN_TAC THEN
  INTRO_TAC "(H0 H1) H2" THEN REPEAT STRIP_TAC THENL [
    FIRST_X_ASSUM MP_TAC THEN REWRITE_TAC[STEPS_ADD] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];

    ASM_CASES_TAC `n' < n1` THENL [
      ASM_MESON_TAC[];

      SUBGOAL_THEN `n' = n1 + (n' - n1)` ASSUME_TAC THENL [
        SIMPLE_ARITH_TAC; ALL_TAC
      ] THEN
      ABBREV_TAC `k = n' - n1` THEN
      UNDISCH_THEN `n' = n1 + k` SUBST_ALL_TAC THEN
      SUBGOAL_THEN `k < n2` ASSUME_TAC THENL [SIMPLE_ARITH_TAC;ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[STEPS_ADD]) THEN ASM_MESON_TAC[]
    ]
  ]);;

let EVENTUALLY_N_STEP =
  prove(
    `!(step:S->S->bool) (P:S->bool) n s.
      eventually_n step (1+n) P s <=>
      ((?s'. step s s') /\
       (!s'. step s s' ==> eventually_n step n P s'))`,
    REWRITE_TAC[eventually_n;STEPS_ADD;STEPS_ONE] THEN
    REPEAT STRIP_TAC THEN EQ_TAC THENL [
      REPEAT STRIP_TAC THENL [
        FIRST_X_ASSUM (fun th -> MP_TAC (SPECL [`s:S`;`0`] th)) THEN
        MESON_TAC[ARITH_RULE`0<1+n`; STEPS_TRIVIAL];

        ASM_MESON_TAC[];

        FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `1+n':num` THEN
        CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_MESON_TAC[STEPS_STEP]
      ];

      REPEAT STRIP_TAC THENL [
        ASM_MESON_TAC[];

        MP_TAC (SPEC `n':num` num_CASES) THEN
        STRIP_TAC THENL [
          ASM_MESON_TAC[STEPS_TRIVIAL];
          UNDISCH_TAC `n' = SUC n''` THEN REWRITE_TAC[ARITH_RULE`!k. SUC k = 1+k`] THEN
          DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC (REWRITE_RULE[STEPS_ADD;STEPS_ONE]) THEN
          SUBGOAL_THEN `n''<n` ASSUME_TAC THENL [ASM_ARITH_TAC;ALL_TAC] THEN
          ASM_MESON_TAC[]
        ]
      ]
    ]);;

let EVENTUALLY_N_STEPS =
  prove(
    `!(step:S->S->bool) P (n:num) s. eventually_n step n P s ==> ?s'. steps step n s s'`,
    MESON_TAC[eventually_n;STEPS_NOSTUCK]);;

let EVENTUALLY_N_MONO =
  prove(
    `!(step:S->S->bool) (P:S->bool) (Q:S->bool) n s.
      (!s'. P s' ==> Q s') ==>
      eventually_n step n P s ==> eventually_n step n Q s`,
    REWRITE_TAC[eventually_n] THEN MESON_TAC[]);;

let EVENTUALLY_N_IMP_EVENTUALLY_N = prove
 (`!(step:S->S->bool) (P:S->bool) (Q:S->bool) n2.
    (!s n1. eventually_n step n1 P s ==> eventually_n step (n1 + n2) Q s) <=>
    (!s. P s ==> eventually_n step n2 Q s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [
    MESON_TAC[EVENTUALLY_N_TRIVIAL; ARITH_RULE `0 + n = n`];
    REWRITE_TAC [eventually_n] THEN
    REPEAT STRIP_TAC THENL [
      ASM_MESON_TAC[STEPS_ADD];
      DISJ_CASES_TAC (ARITH_RULE `n' < n1 \/ n' >= n1`) THENL [
        ASM_MESON_TAC[STEPS_ADD];
        FIRST_X_ASSUM (fun th -> CHOOSE_THEN ASSUME_TAC (REWRITE_RULE [GE; LE_EXISTS] th)) THEN
        ASM_MESON_TAC [LT_ADD_LCANCEL; STEPS_ADD]]]]);;

let EVENTUALLY_N_EVENTUALLY =
  prove(
    `!(step:S->S->bool) (P:S->bool) n s.
      eventually_n step n P s ==> eventually step P s`,
    REPEAT_N 2 GEN_TAC THEN MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL [
      REWRITE_TAC[eventually_n; STEPS_TRIVIAL] THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN MESON_TAC[];

      REWRITE_TAC[ARITH_RULE`SUC n=1+n`] THEN
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> MP_TAC (GEN_REWRITE_RULE I [EVENTUALLY_N_STEP] th)) THEN
      STRIP_TAC THEN
      ONCE_REWRITE_TAC[eventually_CASES] THEN
      DISJ2_TAC THEN
      UNDISCH_TAC `eventually_n (step:S->S->bool) (1+n) P s` THEN
      REWRITE_TAC[eventually_n;STEPS_ADD;STEPS_ONE] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP STEPS_NOSTUCK th)) THEN
      STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[STEPS_ADD;STEPS_ONE]) THEN
      ASM_MESON_TAC[eventually_n]
    ]);;

let EVENTUALLY_N_P_INOUT = prove(
  `!(step:S->S->bool) P Q n s0.
    P /\ eventually_n step n (\s. Q s s0) s0 <=>
    eventually_n step n (\s. P /\ Q s s0) s0`,
  REWRITE_TAC[eventually_n] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
  replicate (MESON_TAC[STEPS_NOSTUCK]) 2);;

(* Inverse direction of this lemma (EVENTUALLY_N_EVENTUALLY_STEPS) is not true.
   Consider three states s0, s1, s2 that forms a triangle:
   (1) s0 -> s1 -> s2
   (2) s0 -> s2
   If P(s2) is true and P(s1) is false, then
   `eventually step (\s'. steps step 1 s s' /\ P s') s0` is true because
   `steps step 1 s0 s0` holds.
   However, `eventually_n step 1 P s` is false because P(s1) is false. *)
let EVENTUALLY_N_EVENTUALLY_STEPS = prove(
  `!(step:S->S->bool) P n s.
    eventually_n step n P s ==> eventually step (\s'. steps step n s s' /\ P s') s`,

  REPEAT_N 2 GEN_TAC THEN INDUCT_TAC THENL [
    REWRITE_TAC[eventually_n] THEN
    ONCE_REWRITE_TAC[eventually_CASES] THEN
    REWRITE_TAC[STEPS_TRIVIAL;ARITH_RULE`!n. ~(n<0)`] THEN
    GEN_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[];

    REWRITE_TAC[ARITH_RULE`SUC n = 1 + n`] THEN
    GEN_TAC THEN
    DISCH_THEN (fun th -> MP_TAC (GEN_REWRITE_RULE I [EVENTUALLY_N_STEP] th)) THEN
    STRIP_TAC THEN ONCE_REWRITE_TAC[eventually_CASES] THEN DISJ2_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[STEPS_ADD;STEPS_ONE] THEN GEN_TAC THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM (fun evth -> ASSUME_TAC (MATCH_MP evth (ASSUME `(step:S->S->bool) s s''`))) THEN
    REWRITE_TAC[ITAUT`((?(x:S). P x) /\ Q) <=> (?x. P x /\ Q)`] THEN
    MATCH_MP_TAC EVENTUALLY_EXISTS THEN
    REWRITE_TAC[GSYM CONJ_ASSOC;GSYM EVENTUALLY_P_INOUT] THEN
    EXISTS_TAC `s'':S` THEN ASM_MESON_TAC[]
  ]);;

(* If the language has deterministic small-step semantics, eventually can be
   used to prove eventually_n. *)
let EVENTUALLY_EVENTUALLY_N = prove(
  `!(step:S->S->bool). (!x y z. step x y /\ step x z ==> y = z) ==>
   !P s. eventually step P s ==> ?n. eventually_n step n P s`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC eventually_INDUCT THEN
  CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[EVENTUALLY_N_TRIVIAL];
    INTRO_TAC "!s; (@s'. HS) IH" THEN
    REMOVE_THEN "IH" (fun ih -> USE_THEN "HS" (CHOOSE_TAC o MATCH_MP ih)) THEN
    EXISTS_TAC `1 + n` THEN
    ASM_MESON_TAC[EVENTUALLY_N_STEP]]);;

(* ------------------------------------------------------------------------- *)
(* Definition and properties of ensures_n.                                   *)
(* ------------------------------------------------------------------------- *)

(* eventually_n version of ensures. *)
let ensures_n = new_definition
  `ensures_n (step:S->S->bool) (precond:S->bool) (postcond:S->bool) (frame:S->S->bool)
             (step_calc:S->num) <=>
    !s. precond s ==> eventually_n step (step_calc s) (\s'. postcond s' /\ frame s s') s`;;

let SEQ_PAIR_SPLIT = prove(
  `!(P:A->A->bool) (Q:A->A->bool) (R:A->A->bool) (S:A->A->bool) p1 p2 p1' p2'.
    ((\(s,s2) (s',s2'). P s s' /\ Q s2 s2') ,, (\(s,s2) (s',s2'). R s s' /\ S s2 s2'))
    (p1,p2) (p1',p2')
    <=>
    ((P ,, R) p1 p1' /\ (Q ,, S) p2 p2')`,
  REWRITE_TAC[seq;EXISTS_PAIR_THM] THEN MESON_TAC[]);;

let ENSURES_N_ENSURES = prove(
  `!(step:S->S->bool) P Q C f_n.
      ensures_n step P Q C f_n ==> ensures step P Q C`,
  REWRITE_TAC[ensures_n;ensures] THEN ASM_MESON_TAC[EVENTUALLY_N_EVENTUALLY]);;

let ENSURES_N_INIT_TAC sname =
  GEN_REWRITE_TAC I [ensures_n] THEN BETA_TAC THEN
  W(fun (asl,w) ->
        let ty = type_of(fst(dest_forall w)) in
        let svar = mk_var(sname,ty) in
        X_GEN_TAC svar THEN
        DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
        ASSUME_TAC(ISPEC svar MAYCHANGE_STARTER));;

let NSUM_REFLECT' = prove(`!x n. nsum (0..n) (\i. x(n - i)) = nsum (0..n) x`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC (SPECL [`x:num->num`; `0`; `n:num`] NSUM_REFLECT) THEN
  REWRITE_TAC[ARITH_RULE `~(n < 0) /\ (n - 0 = n)`]);;

let ENSURES_N_TRIVIAL = prove(
  `!step q f fn. ensures_n step (\x. F) q f fn`,
  REWRITE_TAC[ensures_n]);;

let ENSURES_N_ALREADY = prove(
  `!(step:A->A->bool) P Q C.
    (!s. P s ==> Q s) /\ (=) subsumed C ==> ensures_n step P Q C (\s. 0)`,
  REWRITE_TAC[ensures_n; subsumed; EVENTUALLY_N_TRIVIAL] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]);;

(* If the language has deterministic small-step semantics, ensures can be
   used to prove ensures_n. *)
let ENSURES_ENSURES_N = prove(
  `!(step:S->S->bool) P Q C. (!x y z. step x y /\ step x z ==> y = z) ==>
    ensures step P Q C ==> ?fn. ensures_n step P Q C fn`,
  REWRITE_TAC[ensures; ensures_n; GSYM SKOLEM_THM_GEN] THEN
  SEQ_IMP_REWRITE_TAC[EVENTUALLY_EVENTUALLY_N] THEN
  MESON_TAC[]);;

let ENSURES_N_CONJ = prove(
  `forall (step:S->S->bool) P Q C f_n Q'.
      ensures_n step P Q C f_n /\ ensures_n step P Q' C f_n
      ==> ensures_n step P (\s. Q s /\ Q' s) C f_n`,
  REWRITE_TAC[ensures_n] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM (fun th -> REPEAT (FIRST_X_ASSUM (fun th' -> ASSUME_TAC (MATCH_MP th' th)))) THEN
  POP_ASSUM (fun th -> POP_ASSUM (fun th' -> ASSUME_TAC (MATCH_MP EVENTUALLY_N_CONJ (CONJ th th')))) THEN
  MATCH_MP_TAC (REWRITE_RULE[GSYM IMP_CONJ] EVENTUALLY_N_MONO) THEN
  ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Classic precondition strengthening and postcondition weakening.           *)
(* Implement also (essentially trivial) tactics to apply it.                 *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_PRECONDITION_THM_GEN = prove
 (`!P P' C C' Q fn.
        (!x. P' x ==> P x) /\
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q C' fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_PRECONDITION_THM = prove
 (`!P P' C Q fn.
        (!x. P' x ==> P x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q C fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let ENSURES_N_PRECONDITION_TAC p' =
  MATCH_MP_TAC ENSURES_N_PRECONDITION_THM THEN EXISTS_TAC p';;

let ENSURES_N_POSTCONDITION_THM_GEN = prove
 (`!P C C' Q Q' fn.
        (!x. Q x ==> Q' x) /\
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q' C' fn`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_POSTCONDITION_THM = prove
 (`!P C Q Q' fn.
        (!x. Q x ==> Q' x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q' C fn`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_POSTCONDITION_TAC q' =
  MATCH_MP_TAC ENSURES_N_POSTCONDITION_THM THEN EXISTS_TAC q';;

let ENSURES_N_PREPOSTCONDITION_THM = prove
 (`!P P' C Q Q' fn.
        (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q' C fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The analogous monotonicity result for the frame.                          *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_FRAME_MONO = prove
 (`!P Q C C' fn.
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q C' fn`,
   REPEAT GEN_TAC THEN
   REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
   MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
   ASM_SIMP_TAC[]);;

let ENSURES_N_FRAME_SUBSUMED = prove
 (`!(P:S->bool) Q C C' fn.
        C subsumed C' /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q C' fn`,
   REWRITE_TAC[subsumed; ENSURES_N_FRAME_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Classic Hoare sequencing / Transitivity rule.                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_TRANS = prove(
  `!step (P:S->bool) (Q:S->bool) (R:S->bool) C1 C2 n1 n2.
    ensures_n step P Q C1 (\s. n1) /\ ensures_n step Q R C2 (\s. n2)
    ==> ensures_n step P R (C1 ,, C2) (\s. n1 + n2)`,
  REWRITE_TAC [ensures_n; eventually_n] THEN
  REPEAT_N 11 STRIP_TAC THEN
  CONJ_TAC THENL [
    ASM_MESON_TAC [STEPS_ADD; seq];
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (ARITH_RULE `n' < n1 \/ n' >= n1`) THENL [
      ASM_MESON_TAC [];
      FIRST_X_ASSUM (fun th -> CHOOSE_THEN ASSUME_TAC (REWRITE_RULE [GE; LE_EXISTS] th)) THEN
      ASM_MESON_TAC [LT_ADD_LCANCEL; STEPS_ADD]]]);;

let ENSURES_N_TRANS_SIMPLE = prove(
  `!step (P:S->bool) (Q:S->bool) (R:S->bool) C n1 n2.
    C ,, C = C /\
    ensures_n step P Q C (\s. n1) /\ ensures_n step Q R C (\s. n2)
    ==> ensures_n step P R C (\s. n1 + n2)`,
  MESON_TAC[ENSURES_N_TRANS]);;

let ENSURES_N_SEQUENCE_TAC =
  let pth = prove
   (`!program_decodes pcounter pc' Q n1 n2 n3.
        C ,, C = C /\
        ensures_n step (\s. program_decodes s /\
                          read pcounter s = word pc'' /\
                          P s)
                       (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                          Q s)
                       C (\s. n1) /\
        ensures_n step (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                          Q s)
                       R C (\s. n2) /\
        n3 = n1 + n2
        ==> ensures_n step (\s. program_decodes s /\
                              read pcounter s = word pc'' /\
                              P s)
                           R C (\s. n3)`,
    MESON_TAC[ENSURES_N_TRANS_SIMPLE]) in
  let tac = MATCH_MP_TAC pth in
  fun pc q n1 n2 -> (tac THEN MAP_EVERY EXISTS_TAC [pc;q;n1;n2] THEN BETA_TAC THEN
              CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Induction, basically a variant of the usual WHILE rule with a             *)
(* test at the end. Versions for up from 0...k-1, down from k-1...0 and up   *)
(* from a...b-1.                                                             *)
(* ------------------------------------------------------------------------- *)

let COMPONENT_SINK = prove(`!B. ((\a:A b:B. T) ,, (\a:B b:C. T)) = (\a:A b:C. T)`, REWRITE_TAC [FUN_EQ_THM; seq]);;

let MAYCHANGE_IDEMPOT_TAC' (asl, w as gl) =
  match w with
    Comb(Comb(Const("=", _), Comb(Comb(Const(",,", _), _), _)), Abs(_, Abs(_, Const("T", _)))) ->
      MATCH_ACCEPT_TAC COMPONENT_SINK gl
  | _ -> MAYCHANGE_IDEMPOT_TAC gl;;

let ENSURES_N_WHILE_UP_TAC, ENSURES_N_WHILE_DOWN_TAC,
    ENSURES_N_WHILE_AUP_TAC, ENSURES_N_WHILE_ADOWN_TAC =
  let pth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant 0 s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant k s)
          postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN
    CHOOSE_THEN ASSUME_TAC (GSYM (ISPEC `nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back` EXISTS_REFL)) THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    UNDISCH_THEN `nsum (0..k - 1) (\i. f_nsteps i) + (k - 1) * nsteps_back = x` (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    UNDISCH_THEN `~(k = 0)` (MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC (`k-1:num`,`j:num`) THEN
    REWRITE_TAC [ARITH_RULE `(j + 1) - 1 = j`] THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN REWRITE_TAC [NSUM_SING_NUMSEG; ADD_0; MULT] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG; ADD1; ARITH_RULE `0 <= j + 1`] THEN
      ASM_REWRITE_TAC [ARITH_RULE `(nsum (0..j) (\i. f_nsteps i) + f_nsteps (j + 1)) + (j + 1) * nsteps_back = (nsum (0..j) (\i. f_nsteps i) + (j * nsteps_back)) + f_nsteps (j + 1) + nsteps_back`] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [
        UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j < k`)) THEN
        FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`]);
        SUBST1_TAC (ARITH_RULE `f_nsteps (j + 1) + nsteps_back = nsteps_back + f_nsteps (j + 1)`) THEN
        MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
        ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> 0 < j + 1 /\ j + 1 < k /\ ~(j + 1 = k) /\ ~(j + 1 = 0) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`);
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j + 1 < k /\ ~(j + 1 = k) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`)]]]) in
  let qth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant k s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant 0 s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (k - i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (k - (i + 1))`; `nsteps_back:num`; `nsteps_post:num`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC [ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [ARITH_RULE `k - (i + 1) = (k - 1) - i`; NSUM_REFLECT'; ETA_AX]]) in
  let rth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant a s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\ ~(i = a) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant b s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_back:num`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  let sth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant b s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = a) /\ ~(i = 0) /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant a s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_back:num`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun a b pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun b a pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Variants where there is an extra conjunct in the end state that may       *)
(* not hold at the outset of the zeroth iteration. This is mainly intended   *)
(* for cases where the last arithmetic operation sets flags that are then    *)
(* used to decide the branch.                                                *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_WHILE_PUP_TAC,ENSURES_N_WHILE_PDOWN_TAC,
    ENSURES_N_WHILE_PAUP_TAC,ENSURES_N_WHILE_PADOWN_TAC =
  let pth = prove(
    `!k pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p 0 s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p (i + 1) s /\ q (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p k s /\ q k s)
          postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN
    CHOOSE_THEN ASSUME_TAC (GSYM (ISPEC `nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)` EXISTS_REFL)) THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    UNDISCH_THEN `nsum (0..k - 1) (\i. f_nsteps i) + k - 1 = x` (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    UNDISCH_THEN `~(k = 0)` (MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC (`k-1:num`,`j:num`) THEN
    REWRITE_TAC [ARITH_RULE `(j + 1) - 1 = j`] THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN REWRITE_TAC [NSUM_SING_NUMSEG; ADD_0] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG; ADD1; ARITH_RULE `0 <= j + 1`] THEN
      ASM_REWRITE_TAC [ARITH_RULE `(nsum (0..j) (\i. f_nsteps i) + f_nsteps (j + 1)) + j + 1 = (nsum (0..j) (\i. f_nsteps i) + j) + f_nsteps (j + 1) + 1`] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [
        UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j < k`)) THEN
        FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`]);
        SUBST1_TAC (ARITH_RULE `f_nsteps (j + 1) + 1 = 1 + f_nsteps (j + 1)`) THEN
        MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
        ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> 0 < j + 1 /\ j + 1 < k /\ ~(j + 1 = k) /\ ~(j + 1 = 0) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`);
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j + 1 < k /\ ~(j + 1 = k) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`)]]]) in
  let qth = prove(
    `!k pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p k s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p 0 s /\ q 0 s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (k - i)`; `\i. (q:num->A->bool) (k - i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (k - (i + 1))`; `nsteps_post:num`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC [ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [ARITH_RULE `k - (i + 1) = (k - 1) - i`; NSUM_REFLECT'; ETA_AX]]) in
  let rth = prove(
    `!a b pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p a s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p (i + 1) s /\ q (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\ ~(i = a) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p b s /\ q b s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (a + i)`; `\i. (q:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  let sth = prove(
    `!a b pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p b s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = a) /\ ~(i = 0) /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p a s /\ q a s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (a + i)`; `\i. (q:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  (fun k pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun k pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun a b pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun b a pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Finalize the state, reshuffle and eliminate MAYCHANGE goals.              *)
(* An ensures_n version of ENSURES_FINAL_STATE_TAC.                          *)
(* ------------------------------------------------------------------------- *)

(* A variant of ENSURES_FINAL_STATE_TAC but targets eventually_n. *)
let ENSURES_N_FINAL_STATE_TAC =
  GEN_REWRITE_TAC I [EVENTUALLY_N_TRIVIAL] THEN
  GEN_REWRITE_TAC TRY_CONV [BETA_THM] THEN
  W(fun (asl,w) ->
        let onlycjs,othercjs = partition maychange_term (conjuncts w) in
        if othercjs = [] then
          TRY(REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN NO_TAC)
        else if onlycjs = [] then
          let w' = list_mk_conj othercjs in
          GEN_REWRITE_TAC I [CONJ_ACI_RULE(mk_eq(w,w'))]
        else
          let w' = mk_conj(list_mk_conj othercjs,list_mk_conj onlycjs) in
          (GEN_REWRITE_TAC I [CONJ_ACI_RULE(mk_eq(w,w'))] THEN
           TRY(CONJ_TAC THENL
                [ALL_TAC;
                 REPEAT CONJ_TAC THEN MONOTONE_MAYCHANGE_TAC THEN
                 NO_TAC])));;


(* ------------------------------------------------------------------------- *)
(* Introduce a new ghost variable for a state component in "ensures".        *)
(* An ensures_n version of GHOST_INTRO_TAC.                                  *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_GHOST_INTRO_TAC =
  let pth = prove
   (`forall f (P:S->A->bool) step post frame n.
         (!a. ensures_n step (\s. P s a /\ f s = a) post frame n)
         ==> ensures_n step (\s. P s (f s)) post frame n`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ_ALT; FORALL_UNWIND_THM1]) in
  fun t comp ->
    MP_TAC(ISPEC comp pth) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BETA_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC t THEN
    GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o LAND_CONV o ABS_CONV o TOP_DEPTH_CONV)
     [GSYM CONJ_ASSOC];;


(* ------------------------------------------------------------------------- *)
(* A way of using a lemma for a subroutine or subcomponent.                  *)
(* Tactic supports the basic templating and leaves two user subgoals.        *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_SUBLEMMA_THM = prove
  (`!t (P:A->bool) Q R fn.
         (!s. P s ==> P' s) /\
         R' subsumed R /\
         (!s s'. P s /\ Q' s' /\ R' s s' ==> Q s')
         ==> ensures_n t P' Q' R' fn ==> ensures_n t P Q R fn`,
   REPEAT GEN_TAC THEN REWRITE_TAC[subsumed] THEN STRIP_TAC THEN
   REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN
   X_GEN_TAC `s:A` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
   ASM_SIMP_TAC[] THEN
   MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]
         EVENTUALLY_N_MONO) THEN
   ASM_MESON_TAC[]);;

let ENSURES_N_ENSURES_TAC th =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_N_ENSURES THEN META_EXISTS_TAC THEN
  MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (UNIFY_ACCEPT_TAC [`f_n:armstate->num`]);;


(* ------------------------------------------------------------------------- *)
(* Induction, a variant of the above WHILE loop tactics where the loop body  *)
(* and backedge proofs are combined.                                         *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_WHILE_UP2_TAC, ENSURES_N_WHILE_DOWN2_TAC,
    ENSURES_N_WHILE_AUP2_TAC, ENSURES_N_WHILE_ADOWN2_TAC =
  let pth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant 0 s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word (if i + 1 < k then pc1 else pc2) /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant k s)
          postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + nsum (0..(k-1)) (\i. f_nsteps i) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    DISJ_CASES_TAC (SPEC `k = 0 + 1` EXCLUDED_MIDDLE) THENL [
      ASM_REWRITE_TAC[ARITH_RULE `(0 + 1) - 1 = 0`; NSUM_CLAUSES_NUMSEG] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `0 < 0 + 1 /\ ~(0 + 1 < 0 + 1)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 = SUC (k - 1 - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `0 <= SUC (k - 1 - 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    META_EXISTS_TAC THEN CONJ_TAC THENL [
      ALL_TAC;
      FIRST_X_ASSUM (MP_TAC o SPEC `k:num - 1`) THEN
      SUBGOAL_THEN `k - 1 < k /\ 0 < k /\ ~(k - 1 = k) /\ k - 1 + 1 = k /\ ~(k < k) /\ SUC (k - 1 - 1) = k - 1` (fun th -> ASM_REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (UNIFY_ACCEPT_TAC [`Q:A->bool`])] THEN
    SUBGOAL_THEN `k - 1 - 1 = k - 2 /\ k - 1 = (k - 2) + 1` (fun th -> ONCE_REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 2 < k - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC (`k - 2:num`,`j:num`) THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN REWRITE_TAC[NSUM_SING_NUMSEG; ADD_0; MULT] THEN
      SUBGOAL_THEN `0 < k /\ 0 + 1 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ADD1; ARITH_RULE `0 <= j + 1`] THEN
      IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
      META_EXISTS_TAC THEN CONJ_TAC THENL [
        UNDISCH_THEN `SUC j < k - 1` (MP_TAC o MP (ARITH_RULE `SUC j < k - 1 ==> j < k - 1`)) THEN
        FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`]);
        FIRST_X_ASSUM (MP_TAC o SPEC `j + 1`) THEN
        SUBGOAL_THEN `(j + 1) + 1 < k /\ j + 1 < k /\ ~(j + 1 = k) /\ 0 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[]]]) in
  let qth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant k s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word (if i > 0 then pc1 else pc2) /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant 0 s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + nsum (0..(k-1)) (\i. f_nsteps i) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (k - i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (k - (i + 1))`; `nsteps_post:num`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i /\ (k - (i + 1) > 0 <=> i + 1 < k)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `k - (i + 1) = (k - 1) - i`; NSUM_REFLECT'; ETA_AX]]) in
  let rth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant a s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word (if i + 1 < b then pc1 else pc2) /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant b s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + nsum(a..(b-1)) (\i. f_nsteps i) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN STRIP_TAC THENL [
      GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `a + i`) THEN
      REWRITE_TAC[ARITH_RULE `(a + i) + 1 < b <=> i + 1 < b - a`] THEN
      DISCH_THEN (fun th -> IMP_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  let sth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant b s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word (if i > a then pc1 else pc2) /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant a s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + nsum(a..(b-1)) (\i. f_nsteps i) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN STRIP_TAC THENL [
      GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `a + i`) THEN
      REWRITE_TAC[ARITH_RULE `a + i > a <=> i > 0`] THEN
      DISCH_THEN (fun th -> IMP_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun a b pc1 pc2 iv f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun b a pc1 pc2 iv f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Memory read expression rewriter. This is useful when there is no exactly  *)
(* matching `read (memory :> bytesXX ...) = ..` equality in assumptions but  *)
(* can be somehow inferred from it. MK_MEMORY_READ_EQ_BIGDIGIT_CONV examples *)
(* demonstrate a few useful cases.                                           *)
(* ------------------------------------------------------------------------- *)

(* Given t which is `memory :> bytes (..)` or `memory :> bytes64 (..)`,
   return the address, byte size and constructor name ("bytes64", "bytes", ...).
   Note that this relies on the fact that both armstate and x86state structures
   have the memory field. *)
let get_memory_read_info (t:term): (term * term * string) option =
  if not (is_binary ":>" t) then None else
  let l,r = dest_binary ":>" t in
  let lname,_ = dest_const l in
  if lname <> "memory" then None else
  let c,args = strip_comb r in
  match fst (dest_const c) with
  | "bytes64" ->
    (* args is just a location *)
    assert (List.length args = 1);
    Some (List.hd args, `8`, "bytes64")
  | "bytes128" ->
    (* args is just a location *)
    assert (List.length args = 1);
    Some (List.hd args, `16`, "bytes128")
  | "bytes" ->
    (* args is (loc, len). *)
    assert (List.length args = 1);
    let a, sz = dest_pair (List.hd args) in
    Some (a, sz, "bytes")
  | _ -> (* don't know what it is *)
    None;;

let get_base_ptr_and_ofs (t:term): term * term =
  try (* t is "word_add baseptr (word ofs)" *)
    let baseptr,y = dest_binary "word_add" t in
    let wordc, ofs = dest_comb y in
    if name_of wordc <> "word" then failwith "not word" else
    (baseptr, ofs)
  with _ -> (t, mk_small_numeral 0);;

assert (get_base_ptr_and_ofs `x:int64` = (`x:int64`,`0`));;
assert (get_base_ptr_and_ofs `word_add x (word 32):int64` = (`x:int64`,`32`));;
assert (get_base_ptr_and_ofs `word_add x (word (8*4)):int64` = (`x:int64`,`8*4`));;
(* To get (x, 48) from this, WORD_ADD_ASSOC_CONST must be applied first. *)
assert (get_base_ptr_and_ofs `word_add (word_add x (word 16)) (word 32):int64` =
        (`word_add x (word 16):int64`, `32`));;
assert (get_base_ptr_and_ofs `word_add x (word k):int64` = (`x:int64`, `k:num`));;

let get_base_ptr_and_constofs (t:term): term * int =
  let base,ofs = get_base_ptr_and_ofs t in
  if is_numeral ofs then (base,dest_small_numeral ofs)
  else
    try
      let ofs = rhs (concl (NUM_RED_CONV ofs)) in
      (base,dest_small_numeral ofs)
    with _ -> (t,0);;

assert (get_base_ptr_and_constofs `word_add x (word (8*4)):int64` = (`x:int64`,32));;


let digitize_memory_reads_log = ref false;;

(** See the examples below.
    Input: a term 'read (memory :> ...)' as well as assumptions list.
    Returns: a pair of (the main rewrite rule theorem `t = ...`,
      auxiliary equality rules on memory reads that were needed to derive the
      equality but did not exist in the assumptions. **)
let rec MK_MEMORY_READ_EQ_BIGDIGIT_CONV =
  (* return (pointer, (baseptr and ofs), size, "constructor name", state var) *)
  let get_full_info t =
    match t with
    | Comb (Comb (Const ("read", _), comp), state_var) ->
      begin match get_memory_read_info comp with
      | Some (x,size,constrname) ->
        Some (x,get_base_ptr_and_ofs x,size,constrname,state_var)
      | _ -> None
      end
    | _ -> None in

  let const_num_opt (t:term): int option =
    try if is_numeral t then Some (dest_small_numeral t)
        else Some (dest_small_numeral (rhs (concl (NUM_RED_CONV t))))
    with _ -> None in
  let eight = `8` in
  let rec divide_by_8 t: term option =
    try Some (mk_small_numeral ((Option.get (const_num_opt t)) / 8))
    with _ -> try
      let l,r = dest_binary "*" t in
      if l = eight then Some r else if r = eight then Some l else None
    with _ -> try
      let l,r = dest_binary "+" t in
      match (divide_by_8 l),(divide_by_8 r) with
      | Some l', Some r' -> Some (mk_binary "+" (l',r'))
      | _ -> None
    with _ -> try
      let l,r = dest_binary "-" t in
      match (divide_by_8 l),(divide_by_8 r) with
      | Some l', Some r' -> Some (mk_binary "-" (l',r'))
      | _ -> None
    with _ -> None
    in
  let is_multiple_of_8 t = divide_by_8 t <> None in
  let subtract_num t1 t2: term option =
    if t2 = `0` then Some t1
    else if t1 = t2 then Some `0`
    else
      (* returns: ((sym expr, coeff) list, constant) *)
      let rec decompose_adds t: ((term * int) list) * int =
        try ([], dest_small_numeral t) with _ ->
        try let l,r = dest_binary "+" t in
          let lsyms,lconst = decompose_adds l in
          let rsyms,rconst = decompose_adds r in
          let syms = itlist (fun (lsym,lcoeff) rsyms ->
            if not (exists (fun (rsym,_) -> rsym=lsym) rsyms)
            then rsyms @ [lsym,lcoeff]
            else map (fun (rsym,rcoeff) ->
              if rsym = lsym then (lsym,lcoeff + rcoeff) else (rsym,rcoeff))
              rsyms) lsyms rsyms in
          (syms,lconst+rconst) with _ ->
        try (* note that num's subtraction is a bit complicated because
               num cannot be negative. However, there is a chance
               that even if the intermediate constants are negative the
               final subtracted result is non-negative. Let's hope a good
               luck and anticipate that SIMPLE_ARITH_TAC will solve it
               in the end. *)
          let l,r = dest_binary "-" t in
          let lsyms,lconst = decompose_adds l in
          let rsyms,rconst = decompose_adds r in
          let syms = itlist (fun (lsym,lcoeff) rsyms ->
            if not (exists (fun (rsym,_) -> rsym=lsym) rsyms)
            then rsyms @ [lsym,lcoeff]
            else map (fun (rsym,rcoeff) ->
              if rsym = lsym then (lsym,lcoeff - rcoeff) else (rsym,-rcoeff))
              rsyms) lsyms rsyms in
          (syms,lconst-rconst) with _ ->
        try let l,r = dest_binary "*" t in
          let lconst = dest_small_numeral l in
          let rsyms,rconst = decompose_adds r in
          (map (fun (sym,coeff) -> (sym,coeff * lconst)) rsyms,
           rconst * lconst)
        with _ -> ([t,1],0)
      in
      let syms1,const1 = decompose_adds t1 in
      let syms2,const2 = decompose_adds t2 in
      if syms1 = syms2 && const1 >= const2
      then Some (mk_small_numeral (const1 - const2))
      else None in

  let rec mk_word_add =
    let rec num_add expr (imm:int) =
      if is_numeral expr then
        mk_small_numeral(imm + dest_small_numeral expr)
      else if is_binary "+" expr then
        let l,r = dest_binary "+" expr in
        mk_binary "+" (l,num_add r imm)
      else mk_binary "+" (expr,mk_small_numeral imm) in
    let template = `word_add ptr (word ofs):int64` in
    (fun ptrofs imm ->
      if is_binary "word_add" ptrofs then
        let ptr,ofs = dest_binary "word_add" ptrofs in
        let ofs = mk_word_add ofs imm in
        mk_binop `word_add:int64->int64->int64` ptr ofs
      else if is_comb ptrofs && is_const (fst (dest_comb ptrofs)) &&
              name_of (fst (dest_comb ptrofs)) = "word" then
        let expr = snd (dest_comb ptrofs) in
        mk_comb(`word:num->int64`,num_add expr imm)
      else vsubst [ptrofs,`ptr:int64`;(mk_small_numeral imm),`ofs:num`] template) in
  let mk_read_mem_bytes64 =
    let template = ref None in
    (fun ptrofs state_var ->
      let temp = match !template with
        | None -> begin
            (* The 'memory' constant must be parsable at this point. It is either armstate
               or x86state. *)
            template := Some `read (memory :> bytes64 ptrofs)`;
            !template
          end
        | Some t -> t in
      mkcomb(vsubst [ptrofs,`ptrofs:int64`] template, state_var)) in
  let mk_word_join_128 =
    let wj = `word_join:int64->int64->int128` in
    (fun high low -> (mk_comb ((mk_comb (wj,high)),low))) in

  (* if ptrofs is word_add p (word_sub (word x) (word y)),
      return 'word_add p (word (x - y))' *)
  let canonicalize_word_add_sub ptrofs =
    if not (is_binary "word_add" ptrofs) then None else
    let w,the_rhs = dest_comb ptrofs in
    let the_wordadd,base = dest_comb w in
    if not (is_binary "word_sub" the_rhs) then None else
    let x,y = dest_binary "word_sub" the_rhs in
    if name_of (fst (dest_comb x)) <> "word" ||
       name_of (fst (dest_comb y)) <> "word" then None else
    let (the_word,x),y = dest_comb x,snd (dest_comb y) in
    Some (mk_binop the_wordadd base (mk_comb(the_word,mk_binary "-" (x,y)))) in

  fun (t:term) (assumptions:(string * thm) list): (thm * (thm list)) ->
    match get_full_info t with
    | Some (ptrofs,(ptr, ofs),size,constr_name,state_var) ->
      (* if ptrofs is word_add p (word_sub (word x) (word y)), try to make it
        'word_add p (word (x - y))' *)
      let canon_wordsub_rule = ref None in
      let ptr,ofs = match canonicalize_word_add_sub ptrofs with
      | None -> ptr,ofs
      | Some ptrofs' ->
        try
          let _ = canon_wordsub_rule := Some
            (TAC_PROOF((assumptions,mk_eq(ptrofs,ptrofs')),
              IMP_REWRITE_TAC[WORD_SUB2] THEN SIMPLE_ARITH_TAC)) in
          get_base_ptr_and_ofs ptrofs'
        with _ -> (ptr,ofs)
      in

      if not (is_multiple_of_8 ofs) then
        failwith ("offset is not divisible by 8: `" ^ (string_of_term ofs) ^ "`") else
      (if !digitize_memory_reads_log then
        Printf.printf "digitizing read %s: (`%s`,`%s`), sz=`%s`\n"
          constr_name (string_of_term ptr) (string_of_term ofs)
          (string_of_term size));
      let ofs_opt = const_num_opt ofs in

      if constr_name = "bytes64" then
        let _ = assert (size = eight) in
        let larger_reads = List.filter_map (fun (_,ath) ->
          try
            let c = concl ath in
            if not (is_eq c) then None else
            let c = lhs c in
            let c_access_info = get_full_info c in
            begin match c_access_info with
            | Some (ptrofs2,(ptr2,ofs2),size2,"bytes",state_var2) ->
              begin
              (if !digitize_memory_reads_log then
                Printf.printf "read bytes assum: (`%s`,`%s`), sz=`%s`\n"
                  (string_of_term ptr2) (string_of_term ofs2) (string_of_term size2));
              if (ptr = ptr2 && state_var = state_var2 &&

              begin match ofs_opt,(const_num_opt size2),(const_num_opt ofs2) with
              | Some ofs,Some size2,Some ofs2 ->
                (* everything is constant; easy to determine *)
                (* size must be `8` here *)
                ofs2 <= ofs && ofs + 8 <= ofs2 + size2
              | Some ofs,None,Some ofs2 ->
                (* offsets are constant! *)
                (* size must be `8` here *)
                not (ofs + 8 <= ofs2)
              | _ -> true
              end) then
                Some (ath,Option.get c_access_info)
              else None
              end
            | _ -> None
            end
          with _ ->
            let _ = Printf.printf "Warning: MK_MEMORY_READ_EQ_BIGDIGIT_CONV: unexpected failure: `%s`\n" (string_of_term (concl ath))in
            None) assumptions in
        if larger_reads = []
        then failwith ("No memory read assumption that encompasses `" ^ (string_of_term t) ^ "`") else
        (if !digitize_memory_reads_log then (
          Printf.printf "MK_MEMORY_READ_EQ_BIGDIGIT_CONV: found:\n";
          List.iter (fun th,_ -> Printf.printf "  `%s`\n" (string_of_term (concl th))) larger_reads));

        let extracted_reads = List.filter_map
          (fun larger_read_th,(ptrofs2,(ptr2,ofs2),size2,_,_) ->
          try
            let larger_read = lhs (concl larger_read_th) in
            if not (is_multiple_of_8 ofs2) then
              let _ = if !digitize_memory_reads_log then
                Printf.printf "not multiple of 8: `%s`\n"
                  (string_of_term ofs2) in None else

            let ofsdiff = subtract_num ofs ofs2 in
            let reldigitofs = Option.bind ofsdiff divide_by_8 in
            let nwords = divide_by_8 size2 in

            begin match reldigitofs, nwords with
            | Some reldigitofs, Some nwords ->

              (* t = bigdigit t' ofs *)
              let the_goal = mk_eq(t,mk_comb
                (`word:num->int64`,list_mk_comb (`bigdigit`,[larger_read;reldigitofs]))) in
              begin try

                let eq_th = TAC_PROOF((assumptions,the_goal),
                  (* If t was 'word_add ptr (word_sub ...)', convert it into
                    'word_add (word (.. - ..))'. *)
                  (match !canon_wordsub_rule with | None -> ALL_TAC
                    | Some th -> REWRITE_TAC[th]) THEN
                  SUBGOAL_THEN (subst [size2,`size2:num`;nwords,`nwords:num`] `8 * nwords = size2`) MP_TAC
                  THENL [ ARITH_TAC; DISCH_THEN (LABEL_TAC "H_NWORDS") ] THEN
                  USE_THEN "H_NWORDS" (fun hth -> REWRITE_TAC[REWRITE_RULE[hth]
                    (SPECL [nwords;ptrofs2] (GSYM BIGNUM_FROM_MEMORY_BYTES))]) THEN
                  REWRITE_TAC[BIGDIGIT_BIGNUM_FROM_MEMORY] THEN
                  COND_CASES_TAC THENL [ALL_TAC; SIMPLE_ARITH_TAC (* index must be within bounds *) ] THEN
                  (* read (memory :> bytes64 (expr1)) s =
                     read (memory :> bytes64 (expr2)) s *)
                  REWRITE_TAC[WORD_VAL; WORD_ADD_ASSOC_CONSTS; WORD_ADD_0;
                      MULT_0; LEFT_SUB_DISTRIB; LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
                  (* get the 'expr1 = expr2' *)
                  AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC
                  THEN
                  (SIMPLE_ARITH_TAC ORELSE
                    (* strip word_add *)
                    (AP_TERM_TAC THEN AP_TERM_TAC THEN SIMPLE_ARITH_TAC))) in
                Some (REWRITE_RULE[larger_read_th] eq_th,[])
              with _ ->
                (if !digitize_memory_reads_log then
                  Printf.printf "Could not prove `%s`\n" (string_of_term the_goal)); None
              end
            | _, _ -> begin
              (if !digitize_memory_reads_log then
              Printf.printf "cannot simplify offset difference or nwords; (`%s`-`%s`)/8, `%s`/8\n"
                (string_of_term ofs) (string_of_term ofs2) (string_of_term size2));
              None
            end
            end
          with _ -> begin
            Printf.printf "Warning: MK_MEMORY_READ_EQ_BIGDIGIT_CONV: failed while processing `%s`\n" (string_of_term (concl larger_read_th)); None
          end) larger_reads in

        let _ = if length extracted_reads > 1 then
          Printf.printf "Warning: There are more than one memory read assumption that encompasses `%s`\n"
              (string_of_term t) in
        (if !digitize_memory_reads_log then begin
          Printf.printf "MK_MEMORY_READ_EQ_BIGDIGIT_CONV: extracted:\n";
          List.iter (fun th,_ ->
            Printf.printf "  `%s`\n" (string_of_term (concl th))) extracted_reads
        end);
        List.hd extracted_reads

      else if constr_name = "bytes128" then
        (* bytes128 to word_join of two bytes64 reads *)
        let readl = mk_read_mem_bytes64 ptrofs state_var in
        let readh = mk_read_mem_bytes64 (mk_word_add ptrofs 8) state_var in
        let construct_bigdigit_rule t =
          match List.find_opt (fun _,asm -> let c = concl asm in is_eq c && lhs c = t) assumptions with
          | None -> MK_MEMORY_READ_EQ_BIGDIGIT_CONV t assumptions
          | Some (_,ath) -> (ath,[]) in
        let readl_th,extra_ths1 = construct_bigdigit_rule readl in
        let readh_th,extra_ths2 = construct_bigdigit_rule readh in
        (* word_join readh_th readl_th *)
        let the_goal =
          let readl = rhs (concl readl_th) and readh = rhs (concl readh_th) in
          mk_eq (t,mk_word_join_128 readh readl) in
        let result =
          let new_assums = readl_th::readh_th::(extra_ths1 @ extra_ths2) in
          TAC_PROOF((map (fun th -> ("",th)) new_assums,the_goal),
            ASM_REWRITE_TAC[el 1 (CONJUNCTS READ_MEMORY_BYTESIZED_SPLIT)] THEN
            FAIL_TAC "could not synthesize bytes128 from join(bytes64,bytes64)") in
        (* Eliminate the assumptions that are readl_th and readh_th, and put assumptions
           that readl_th and readh_th were relying on. *)
        let result = PROVE_HYP readh_th (PROVE_HYP readl_th result) in
        (result, readl_th::readh_th::(extra_ths1 @ extra_ths2))

      else failwith ("cannot deal with size `" ^ (string_of_term size) ^ "`")
    | None -> failwith "not memory read";;

(*** examples ***)
(*
MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 x) s`
    ["",new_axiom `read (memory :> bytes (x:int64,32)) s = k`];;
(* (|- read (memory :> bytes64 x) s = word (bigdigit k 0), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word 16))) s`
    ["",new_axiom `read (memory :> bytes (word_add x (word 8):int64,32)) s = k`];;
(* (|- read (memory :> bytes64 (word_add x (word 16))) s = word (bigdigit k 1), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word 16))) s`
    ["",new_axiom `read (memory :> bytes (word_add x (word 8):int64,8 * 4)) s = k`];;
(* (|- read (memory :> bytes64 (word_add x (word 16))) s = word (bigdigit k 1), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word 16))) s`
    ["",new_axiom `read (memory :> bytes (word_add x (word 8):int64,8 * n)) s = k`;
     "",new_axiom `n > 3`];;
(* (|- read (memory :> bytes64 (word_add x (word 16))) s = word (bigdigit k 1), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word (8 * 2)))) s`
    ["",new_axiom `read (memory :> bytes (word_add x (word (8 * 1)):int64,8 * n)) s = k`;
     "",new_axiom `n > 3`];;
(* (|- read (memory :> bytes64 (word_add x (word (8 * 2)))) s = word (bigdigit k 1), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word (8 * 2)))) s`
    ["",new_axiom `read (memory :> bytes (x:int64,8 * 2)) s = k`;
     "",new_axiom `read (memory :> bytes (word_add x (word (8 * 2)):int64,8 * n)) s = k2`;
     "",new_axiom `read (memory :> bytes (word_add x (word (8 * 4)):int64,8 * n)) s = k2`;
     "",new_axiom `n > 3`];;
(* (|- read (memory :> bytes64 (word_add x (word (8 * 2)))) s = word (bigdigit k2 0), []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes64 (word_add x (word (8 * i)))) s`
    ["",new_axiom `read (memory :> bytes (x:int64,8 * n)) s = k`;
     "",new_axiom `i < n`];;
(* (|- read (memory :> bytes64 (word_add x (word (8 * i)))) s =
    word (bigdigit k i),
 []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV
    `read (memory :> bytes64 (word_add z (word (8 * (4 * k4 - 4) + 24)))) s`
    ["",new_axiom `read (memory :> bytes (word_add z (word (8 * (4 * k4 - 4))),8 * 4)) s = a`;
     "",new_axiom `read (memory :> bytes (z,8 * (4 * k4 - 4))) s = b`];;
(* (|- read (memory :> bytes64 (word_add z (word (8 * (4 * k4 - 4) + 24)))) s =
    word (bigdigit a 3),
 []) *)

MK_MEMORY_READ_EQ_BIGDIGIT_CONV
    `read (memory :> bytes64
      (word_add m_precalc (word_sub (word (8 * 12 * (k4 - 1))) (word 8))))
     s`
    ["",new_axiom`read (memory :> bytes (m_precalc,8 * 12 * (k4 - 1))) s = k`;
     "",new_axiom`1 < k4`];;
(* (|- read
    (memory :>
     bytes64
     (word_add m_precalc (word_sub (word (8 * 12 * (k4 - 1))) (word 8))))
    s =
    word (bigdigit k (12 * (k4 - 1) - 1)),
 []) *)


MK_MEMORY_READ_EQ_BIGDIGIT_CONV
  `read (memory :> bytes64 (word_add z (word (8 * 4 * (i' + 1) + 24)))) s`
  ["",
   new_axiom
    `read (memory :> bytes (word_add z (word (8 * 4 * (i' + 1))),32)) s =
     a`]

** bytes128 **

MK_MEMORY_READ_EQ_BIGDIGIT_CONV `read (memory :> bytes128 (word_add x (word (8 * 2)))) s`
    ["",new_axiom `read (memory :> bytes (x:int64,8 * 2)) s = k`;
     "",new_axiom `read (memory :> bytes (word_add x (word (8 * 2)):int64,8 * n)) s = k2`;
     "",new_axiom `read (memory :> bytes (word_add x (word (8 * 4)):int64,8 * n)) s = k2`;
     "",new_axiom `n > 3`];;
(* (|- read (memory :> bytes128 (word_add x (word (8 * 2)))) s =
    word_join (word (bigdigit k2 1)) (word (bigdigit k2 0)),
 [|- read (memory :> bytes64 (word_add x (word (8 * 2)))) s =
     word (bigdigit k2 0);
  |- read (memory :> bytes64 (word_add x (word 24))) s = word (bigdigit k2 1)])) *)
*)

(** DIGITIZE_MEMORY_READS will return (thm * (thm option)) where
    1. the first thm is the simplified read statements using bigdigit and
       conjoined with /\
    2. newly constructed equalities between memory reads and bigdigits, returned
       as the second component of MK_MEMORY_READ_EQ_BIGDIGIT_CONV, and conjoined
       with /\. **)
let DIGITIZE_MEMORY_READS th state_update_th =
  fun (asl,w):(thm * (thm option)) ->
    let new_memory_reads: thm list ref = ref [] in
    let ths = map (fun th2 ->
      try
        (* rhs is the memory read to digitize *)
        let the_rhs = rhs (concl th2) in
        let th2',smaller_read_ths = MK_MEMORY_READ_EQ_BIGDIGIT_CONV the_rhs asl in
        let _ = new_memory_reads := th2'::(smaller_read_ths @ !new_memory_reads) in
        GEN_REWRITE_RULE RAND_CONV [th2'] th2
      with _ -> th2) (CONJUNCTS th) in

    (* new_memory_reads will still use the 'previous' state. update it. *)
    new_memory_reads := map
      (fun th -> try STATE_UPDATE_RULE state_update_th th with _ -> th)
      !new_memory_reads;

    let res_th = end_itlist CONJ ths in
    let newmems_th = if !new_memory_reads = [] then None
      else Some (end_itlist CONJ !new_memory_reads) in
    let _ = if !digitize_memory_reads_log then
       (Printf.printf "original th: %s\n" (string_of_term (concl th));
        Printf.printf "rewritten th: %s\n" (string_of_term (concl res_th));
        Printf.printf "new_memory_reads th: %s\n"
          (if newmems_th = None then "None" else
            ("Some " ^ (string_of_term (concl (Option.get newmems_th)))))) in
    res_th,newmems_th;;
