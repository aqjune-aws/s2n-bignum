let add1_mc = define_assert_from_elf "add1_mc" "add1.o"
[
  0x8b020023        (* arm_ADD X3 X1 X2 *)
];;
let ADD1_EXEC = ARM_MK_EXEC_RULE add1_mc;;

let add2_mc = define_assert_from_elf "add2_mc" "add2.o" [
  0x8b010043        (* arm_ADD X3 X2 X1 *)
];;
let ADD2_EXEC = ARM_MK_EXEC_RULE add2_mc;;


(* w must be `expr = x` where x is a meta variable *)
let UNIFY_REFL_TAC (asl,w:goal): goalstate =
  let w_lhs,w_rhs = dest_eq w in
  let insts = term_unify [w_rhs] w_lhs w_rhs in
  ([],insts),[],
  let th_refl = REFL w_lhs in
  fun i [] -> INSTANTIATE i th_refl;;

let UNIFY_REFL_TAC_TEST = prove(`?x. 1 = x`, META_EXISTS_TAC THEN UNIFY_REFL_TAC);;



(* ADD1_ADD2_MC_EQ proves that there exists c s.t. the outputs are equivalent.
   Note that, this definition of equivalence uses existential quantification on
   the final state. This means that it relies on the fact that there isn't
   nondeterminism in the behavior of ADD1 and ADD2. In other words, if executing
   ADD1 from some initial state results in some output state, the output state
   must be the only state that is reachable from the initial state (same for ADD2).
   I found that in CompCert this is called 'determinacy'.
   If there is nondeterminism in the two programs' behavior, then this definition
   is wrong and may admit two non-equivalent programs.
*)
let ADD1_ADD2_MC_EQ = prove(`!pc pc2 a b.
  ?c.
    ensures arm
      (\s. aligned_bytes_loaded s (word pc) add1_mc /\
          read PC s = word(pc) /\
          read X1 s = a /\ read X2 s = b)
      (\s. read PC s = word(pc+4) /\ read X3 s = c)
      (MAYCHANGE [PC; X3])
    /\
    ensures arm
      (\s. aligned_bytes_loaded s (word pc2) add2_mc /\
          read PC s = word(pc2) /\
          read X1 s = a /\ read X2 s = b)
      (\s. read PC s = word(pc2+4) /\ read X3 s = c)
      (MAYCHANGE [PC; X3])`,

  REPEAT STRIP_TAC THEN
  (* Use META_EXISTS_TAC to avoid manually describing the final expression of X3 *)
  META_EXISTS_TAC THEN
  CONJ_TAC THENL [
    ARM_SIM_TAC ADD1_EXEC [1] THEN UNIFY_REFL_TAC;

    ARM_SIM_TAC ADD2_EXEC [1] THEN CONV_TAC WORD_RULE]);;
