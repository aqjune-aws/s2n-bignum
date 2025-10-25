(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(*   Common tactics for proving constant-time and memory-safety properties.  *)
(*  Assumes that this file will be loaded after necessary assembly semantics *)
(*  is loaded ({arm,x86}/proofs/...), as common/bignum.ml does).             *)
(* ========================================================================= *)

needs "common/equiv.ml";;

(* Find the base pointer and access size. *)
let find_stack_access_size (fnspec_maychange:term): (term * int) option =
  try
    let stackptr = mk_var("stackpointer",`:int64`) in

    let t = find_term (fun t -> is_pair t &&
        let baseptr, sz = dest_pair t in
        baseptr = stackptr ||
        (is_binary "word_sub" baseptr &&
         let a,b = dest_binary "word_sub" baseptr in
         a = stackptr)) fnspec_maychange in
    let baseptr,sz = dest_pair t in
    Some (baseptr, dest_small_numeral sz)
  with _ -> None;;

find_stack_access_size `MAYCHANGE [memory :> bytes (stackpointer,264)]`;;
find_stack_access_size `MAYCHANGE [memory :> bytes(z,8 * 8);
                    memory :> bytes(word_sub stackpointer (word 224),224)]`;;

(* Create a safety spec. This returns a safety spec using ensures, as well
   as the unversally quantified variables that are public information. *)
let gen_mk_safety_spec
    ?(coda_pc_range:(int*int) option) (* when coda is used: (begin, len) *)
    (fnargs,_,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec
    (find_eq_stackpointer:term->bool)
    (find_eq_returnaddress:term->bool): term*(term list) =

  (* Decompose the functional correctness. *)
  let fnspec:term = concl subroutine_correct_th in
  let fnspec_quants,t = strip_forall fnspec in
  let (fnspec_globalasms:term),(fnspec_ensures:term) =
      if is_imp t then dest_imp t else `true`,t in
  let arch_const::fnspec_precond::fnspec_postcond::fnspec_maychanges::[] =
      snd (strip_comb fnspec_ensures) in
  let fnspec_precond_bvar,fnspec_precond = dest_abs fnspec_precond in
  let fnspec_postcond_bvar,fnspec_postcond = dest_abs fnspec_postcond in
  (* :x86state or :armstate *)
  let state_ty = fst (dest_fun_ty (type_of arch_const)) in

  let c_args = find_term
    (fun t -> is_comb t && let c,a = dest_comb t in
      name_of c = "C_ARGUMENTS")
      fnspec_precond in
  let c_var_to_hol (var_c:string): term =
    let c_to_hol_vars = zip fnargs (dest_list (rand c_args)) in
    let c_to_hol_vars = map (fun ((x,_,_),yvar) -> x,yvar) c_to_hol_vars in
    try
      assoc var_c c_to_hol_vars
    with _ -> failwith ("c_var_to_hol: unknown var in C: " ^ var_c) in

  let bytes_term = find_term
    (fun t -> is_comb t && let name = name_of (fst (strip_comb t)) in
        name = "bytes_loaded" || name = "aligned_bytes_loaded")
      fnspec_precond in
  let read_sp_eq: term option = try
      Some (find_term find_eq_stackpointer fnspec_precond)
    with _ -> None in
  let stack_access_size: (term*int) option =
      find_stack_access_size fnspec_maychanges in
  assert ((read_sp_eq = None) = (stack_access_size = None));

  let returnaddress_var:term option =
    List.find_opt (fun t -> name_of t = "returnaddress") fnspec_quants in
  let read_x30_eq: term option = try
      Some (find_term find_eq_returnaddress fnspec_precond)
    with _ -> None in

  let elemsz_to_hol (s:string): term =
    let s = if String.starts_with ~prefix:">=" s
      then String.sub s 2 (String.length s - 2) else s in
    try mk_small_numeral (int_of_string s)
    with _ ->
      let v = c_var_to_hol s in
      match dest_type (type_of v) with
      | ("num",_) -> v
      | _ -> (* word ty *) mk_icomb (`val:(N)word->num`,v) in

  (* memreads/writes without stackpointer and pc; (base pointer, size) list. *)
  let (memreads:(term*term)list), (memwrites:(term*term)list) =
    let fn = 
      (fun (c_varname,range,elemty_size) ->
        c_var_to_hol c_varname,
        mk_binary "*" (elemsz_to_hol range, mk_small_numeral elemty_size)) in

    map fn (meminputs @ memoutputs @ memtemps),
    map fn (memoutputs @ memtemps) in

  (* Variables describing public information. *)
  let public_vars = itlist (fun (baseptr,sz) l ->
    let pvars = find_terms is_var baseptr in
    let szvars = find_terms is_var sz in
    union (union pvars l) szvars) (memreads @ memwrites) [] in

  (* Create the f_events var as well as expressions (not necessarily var)
     as args of f_events containing public information *)
  let f_events_public_args = public_vars @
    (match stack_access_size with
     | None -> [`pc:num`] @ (Option.to_list returnaddress_var)
     | Some (baseptr,sz) ->
       [`pc:num`;baseptr] @ (Option.to_list returnaddress_var)) in
  let f_events = mk_var("f_events",
    itlist mk_fun_ty (map type_of f_events_public_args) `:(uarch_event)list`) in

  (* memreads,memwrites with stackpointer as well as pc :) *)
  let memreads,memwrites =
    match stack_access_size with
    | None -> memreads,memwrites
    | Some (baseptr,sz) ->
      (memreads @ [baseptr,mk_small_numeral sz],
       memwrites @ [baseptr,mk_small_numeral sz]) in
  let memreads,memwrites =
    match coda_pc_range with
    | None -> memreads,memwrites
    | Some (pos,sz) ->
      let baseptr = subst [mk_small_numeral pos,`n:num`] `word_add (word pc) (word n):int64` in
      (memreads @ [baseptr,mk_small_numeral sz],
       memwrites @ [baseptr,mk_small_numeral sz]) in

  let s = mk_var("s",state_ty) in
  let precond =
    let read_pc_eq = find_term (fun t -> is_eq t && is_read_pc (lhs t))
        fnspec_precond in
    let read_pc_eq = vsubst [s,fnspec_precond_bvar] read_pc_eq in
    mk_gabs(s,
      list_mk_conj ([
        vsubst [s,s] bytes_term;
        read_pc_eq;
      ] @
      (match read_sp_eq with | None -> [] | Some t -> [ vsubst [s,s] t ]) @
      (match read_x30_eq with | None -> [] | Some t -> [ vsubst [s,s] t ]) @
      [ mk_comb (c_args, s); `read events s = e`; ])) in

  let postcond = mk_gabs(s,
    let mr = mk_list (map mk_pair memreads,`:int64#num`) in
    let mw = mk_list (map mk_pair memwrites,`:int64#num`) in
    let e2 = mk_var("e2",`:(uarch_event)list`) in
    let read_pc_eq = find_term (fun t -> is_eq t && is_read_pc (lhs t))
        fnspec_postcond in
    let read_pc_eq = vsubst [s,fnspec_postcond_bvar] read_pc_eq in
    mk_exists(e2,
      list_mk_conj [
        read_pc_eq;
        `read events s = APPEND e2 e`;
        mk_eq(e2, list_mk_comb (f_events,f_events_public_args));
        mk_comb(mk_comb(mk_comb (`memaccess_inbounds`,e2),mr),mw)
      ])) in

  (* Filter unused forall vars *)
  let spec_without_quantifiers =
    let body = list_mk_icomb "ensures"
        [arch_const;precond;postcond;
        mk_abs(mk_var("s",state_ty), mk_abs(mk_var("s'",state_ty), `true`))] in
    if fnspec_globalasms = `true` then body
    else mk_imp(fnspec_globalasms,body) in
  let the_e_var = mk_var("e", `:(uarch_event)list`) in
  let fnspec_quants_filtered =
    let fvars = frees spec_without_quantifiers in
      the_e_var::List.filter (fun t -> mem t fvars) fnspec_quants in

  (* Return the spec, as well as the HOL Light variables having public info *)
  (mk_exists(f_events,
    list_mk_forall(fnspec_quants_filtered, spec_without_quantifiers)),
   the_e_var::`pc:num`::public_vars @ Option.to_list returnaddress_var @
      (if read_sp_eq = None then [] else [`stackpointer:int64`]));;

let REPEAT_GEN_AND_OFFSET_STACKPTR_TAC =
  W (fun (asl,w) ->
    (match find_stack_access_size w with
    | None -> REPEAT GEN_TAC
    | Some (baseptr,sz) ->
      if is_binary "word_sub" baseptr then
        (REPEAT (W (fun (asl,w) ->
        let x,_ = dest_forall w in
        if name_of x = "stackpointer" then NO_TAC else GEN_TAC)) THEN
        WORD_FORALL_OFFSET_TAC sz THEN
        REPEAT GEN_TAC)
      else if is_var baseptr then GEN_TAC
      else failwith
        ("Don't know how to rebase offset of stackptr " ^
         (string_of_term baseptr))) THEN
    REPEAT GEN_TAC);;

(* Given a conclusion which is
  memaccess_inbounds [..(events)..] [..] [] where events is a list of
  Event* constructors (EventJump, EventLoad, ...), discharge the goal.
*)
let DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC =
  REWRITE_TAC[memaccess_inbounds;ALL;EX] THEN
  REPEAT CONJ_TAC THEN
    (REPEAT ((DISJ1_TAC THEN CONTAINED_TAC) ORELSE DISJ2_TAC ORELSE
            CONTAINED_TAC));;

let DISCHARGE_MEMACCESS_INBOUNDS_TAC =
  let cons_to_append_th =
      MESON[APPEND]
        `memaccess_inbounds (CONS a b) = memaccess_inbounds (APPEND [a] b)` in
  let discharge_using_asm_tac:tactic =
    FIRST_X_ASSUM (fun th ->
    find_term (fun t -> name_of t = "memaccess_inbounds") (concl th);
    MP_TAC th) THEN ASM_REWRITE_TAC[] THEN NO_TAC in
  (* Case 1. If the exactly same memaccess_inbounds exists as assumption,
     just use it. *)
   (discharge_using_asm_tac) ORELSE

  (* Case 2. if the goal is simply a concrete list of events, use an
     existing tactic. *)
   (DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC THEN NO_TAC) ORELSE

  (* Caes 3. If the goal consist of memaccess_inbounds of a previous trace which
     can be discharged by assumption, preceded by a concrete events list,
     apply MEMACCESS_INBOUNDS_APPEND and prove it *)
   ((*REWRITE_TAC[cons_to_append_th] THEN*)
    (* Move the inner CONS to the outermost place *)
    REWRITE_TAC[APPEND] THEN
    (* Convert the CONS sequence in the first argument of memaccess_inbounds to
       APPEND *)
    CONV_TAC ((RATOR_CONV o RATOR_CONV o RAND_CONV) CONS_TO_APPEND_CONV) THEN

    GEN_REWRITE_TAC I [MEMACCESS_INBOUNDS_APPEND] THEN
    CONJ_TAC THENL [
      (* The new, concrete event trace. *)
      DISCHARGE_CONCRETE_MEMACCESS_INBOUNDS_TAC;
      (* The existing event trace. *)
      discharge_using_asm_tac
    ]);;

let mk_freshvar =
  let n = ref 0 in
  fun ty ->
    let s = "trace_" ^ (string_of_int !n) in
    n := 1 + !n;
    mk_var(s,ty);;

let ABBREV_TRACE_TAC (stored_abbrevs:thm list ref)=
  let pat = `read events s = e` in

  let PROVE_MEMORY_INBOUNDS_TAC (trace:term):tactic =
    fun (asl,w) ->
      let mem_inbounds_term =
        find_term
          (fun t -> name_of (fst (strip_comb t)) = "memaccess_inbounds")
          w in
      let c,_::readranges::writeranges::[] = strip_comb mem_inbounds_term in
      let new_mem_inbounds =
          list_mk_comb(c,trace::readranges::writeranges::[]) in
      (SUBGOAL_THEN new_mem_inbounds MP_TAC THENL [
        DISCHARGE_MEMACCESS_INBOUNDS_TAC THEN
        PRINT_GOAL_TAC THEN
        FAIL_TAC "could not prove memaccess_inbounds";
        ALL_TAC
      ] THEN DISCARD_MATCHING_ASSUMPTIONS [`memaccess_inbounds x rr wr`] THEN
      DISCH_TAC) (asl,w) in

  let CORE_ABBREV_TRACE_TAC (trace:term):tactic =
    fun (asl,w) ->
      let f_events_term =
        find_term
          (fun t -> name_of (fst (strip_comb t)) = "f_events")
          w in
      let fv,args = strip_comb f_events_term in
      let fv = mk_freshvar (type_of fv) in
      let newvarth = ref TRUTH in
       (ABBREV_TAC (mk_eq (fv,list_mk_abs(args,trace))) THEN
        POP_ASSUM (fun th ->
          newvarth := th; stored_abbrevs := th::!stored_abbrevs; ALL_TAC) THEN
        SUBGOAL_THEN (mk_eq (trace, list_mk_comb(fv,args))) MP_TAC THENL [
          (fun (asl,w) -> REWRITE_TAC[GSYM !newvarth] (asl,w)) THEN NO_TAC;
          ALL_TAC
        ] THEN
        DISCH_THEN SUBST_ALL_TAC)
      (asl,w) in

  (* Pick `read events .. = rhs`, show `memaccess_inbounds rhs [..] []`,
      and abbreviate it. *)
  RULE_ASSUM_TAC (CONV_RULE (TRY_CONV (
    (fun t -> check is_eq t; ALL_CONV t) THENC
    RAND_CONV CONS_TO_APPEND_CONV))) THEN
  RULE_ASSUM_TAC (REWRITE_RULE [APPEND_ASSOC]) THEN
  fun (asl,w) ->
    let read_events = filter (fun (_,th) ->
      can (term_match [] pat) (concl th)) asl in
    match read_events with
    | [] -> failwith "No read events"
    | (_,read_event_th)::_ ->
      let r = rhs (concl read_event_th) in
      (if is_comb r then
        let trace_append,trace::_::[] = strip_comb r in
        if name_of trace_append <> "APPEND" then failwith "unknown form" else
        (PROVE_MEMORY_INBOUNDS_TAC trace THEN
        CORE_ABBREV_TRACE_TAC trace)
      else
        (* It seems the event list is already well-abbreviated; return *)
        ALL_TAC)
      (asl,w);;

let rec WHILE_TAC (flag:bool ref) tac w =
  (if !flag then tac THEN WHILE_TAC flag tac else ALL_TAC) w;;

(* public_vars describe the HOL Light variables that will contain public
   information. This is for faster symbolic simulation. *)
let GEN_PROVE_SAFETY_SPEC =
  let pth =
    prove(`forall (e:(uarch_event)list) e2.
        e = APPEND e2 e <=> APPEND [] e = APPEND e2 e`,
    MESON_TAC[APPEND]) in
  let qth =
    prove(`memaccess_inbounds [] [] []`, MESON_TAC[memaccess_inbounds;ALL]) in

  let mainfn ?(public_vars:term list option) exec
    (extra_unpack_thms:thm list)
    single_step_tac
    :tactic =
    W (fun (asl,w) ->
      let f_events = fst (dest_exists w) in
      let quantvars,forall_body = strip_forall(snd(dest_exists w)) in
      let stored_abbrevs = ref [] in

      (* The destination PC *)
      let dest_pc_addr =
        let triple = if is_imp forall_body
          then snd (dest_imp forall_body) else forall_body in
        let _,(sem::pre::post::frame::[]) = strip_comb triple in
        let read_pc_eq = find_term (fun t -> is_eq t && is_read_pc (lhs t)) post in
        snd (dest_eq read_pc_eq) in

      X_META_EXISTS_TAC f_events THEN
      REWRITE_TAC[C_ARGUMENTS;ALL;ALLPAIRS;NONOVERLAPPING_CLAUSES;fst exec] THEN
      REWRITE_TAC extra_unpack_thms THEN
      REPEAT_GEN_AND_OFFSET_STACKPTR_TAC THEN
      TRY DISCH_TAC THEN
      REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN

      ENSURES_INIT_TAC "s0" THEN
      (* Drop any 'read .. = ..' statement that does not have any public_var *)
      (match public_vars with
      | None -> ALL_TAC
      | Some public_vars ->
        DISCARD_ASSUMPTIONS_TAC (fun th ->
            let t = concl th in
            is_eq t && is_binary "read" (lhs t) &&
            intersect (frees t) public_vars = [])) THEN

      let chunksize = 50 in
      let i = ref 0 in
      let successful = ref true and hasnext = ref true in
      WHILE_TAC hasnext (W (fun (asl,w) ->
        REPEAT_N chunksize (W (fun (asl,w) ->
          (* find 'read RIP/PC ... = ..' and check it reached at dest_pc_addr *)
          match List.find_opt (fun (_,th) ->
              is_eq (concl th) && is_read_pc (lhs (concl th)))
              asl with
          | None ->
            successful := false; hasnext := false; ALL_TAC
          | Some (_,read_pc_th) ->
            if rhs (concl read_pc_th) = dest_pc_addr
            then (* Successful! *) (hasnext := false; ALL_TAC)
            else (* Proceed *)
              let _ = i := !i + 1 in
              single_step_tac exec ("s" ^ string_of_int !i)))
        THEN

        SIMPLIFY_MAYCHANGES_TAC THEN
        ABBREV_TRACE_TAC stored_abbrevs THEN CLARIFY_TAC)) THEN

      W (fun (asl,w) ->
        if not !successful
        then FAIL_TAC ("could not reach to the destination pc (" ^ (string_of_term dest_pc_addr) ^ ")")
        else ALL_TAC) THEN

      ENSURES_FINAL_STATE_TAC THEN
      ASM_REWRITE_TAC[] THEN
      W (fun (asl,w) -> REWRITE_TAC(map GSYM !stored_abbrevs)) THEN

      (* e2 can be []! *)
      REWRITE_TAC[pth] THEN
      X_META_EXISTS_TAC `e2:(uarch_event)list` THEN
      CONJ_TAC THENL [
        AP_THM_TAC THEN AP_TERM_TAC THEN
        REWRITE_TAC[APPEND] THEN UNIFY_REFL_TAC;
        ALL_TAC
      ] THEN
      (* e2 = f_events <public info> *)
      CONJ_TAC THENL [UNIFY_REFL_TAC; ALL_TAC] THEN
      (* memaccess_inbounds *)
      (ACCEPT_TAC qth ORELSE
      (POP_ASSUM MP_TAC THEN
       W (fun (asl,w) -> REWRITE_TAC(APPEND :: (map GSYM !stored_abbrevs))) THEN
       PRINT_GOAL_TAC THEN FAIL_TAC "Could not prove memaccess_inbounds")))
  in mainfn;;

let ASSERT_GOAL_TAC (t:term): tactic =
  PRINT_GOAL_TAC THEN
  fun (asl,w) ->
    if t <> w then failwith "ASSERT_GOAL_TAC"
    else ALL_TAC (asl,w);;
