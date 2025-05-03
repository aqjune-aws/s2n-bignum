needs "arm/proofs/equiv.ml";;

let mk_safety_spec (fnargs,_,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec =

  let get_c_elemtysize varname =
    let _,s,_ = find (fun name,_,_ -> name = varname) fnargs in
    if String.starts_with ~prefix:"uint64_t" s then 8
      else failwith "c_elemtysize" in

  let fnspec = concl subroutine_correct_th in
  let fnspec_quants,t = strip_forall fnspec in
  assert (name_of (last fnspec_quants) = "returnaddress");
  let fnspec_globalasms,fnspec_ensures =
      if is_imp t then dest_imp t else `true`,t in

  let c_args = find_term
    (fun t -> is_comb t && let c,a = dest_comb t in
      name_of c = "C_ARGUMENTS")
      fnspec_ensures in
  let aligned_bytes_term = find_term
    (fun t -> is_comb t && fst (strip_comb t) = `aligned_bytes_loaded`)
      fnspec_ensures in
  let readsp: term option = try
      Some (find_term
        (fun t -> is_eq t && let l = fst (dest_eq t) in
          is_binary "read" l &&
          fst (dest_binary "read" l) = `SP`)
        fnspec_ensures)
    with _ -> None in

  let memreads = map (fun (varname,range) ->
      find (fun t -> name_of t = varname) fnspec_quants,
      mk_small_numeral(int_of_string range * get_c_elemtysize varname))
    (meminputs @ memoutputs @ memtemps) in
  let memwrites = map (fun (varname,range) ->
      find (fun t -> name_of t = varname) fnspec_quants,
      mk_small_numeral(int_of_string range * get_c_elemtysize varname))
    (memoutputs @ memtemps) in

  let usedvars = itlist (fun (t,_) l -> insert t l) (memreads @ memwrites) [] in
  let numinsts = Array.length (snd exec) / 4 in

  let f_events = mk_var("f_events",
    itlist mk_fun_ty ((map type_of usedvars) @ [`:num`(*pc*);`:int64`(*returnaddress*)])
      `:(armevent)list`) in

  let s1,s2 = mk_var("s1",`:armstate`),mk_var("s2",`:armstate`) in
  let precond = mk_gabs(mk_pair(s1,s2),
    list_mk_conj ([
      vsubst [s1,`s:armstate`] aligned_bytes_term;
      `read PC s1 = word pc`;
      vsubst [s2,`s:armstate`] aligned_bytes_term;
      `read PC s2 = word pc`;
      `read X30 s1 = returnaddress`;
      `read X30 s2 = returnaddress`;
    ] @
    (match readsp with
     | None -> []
     | Some t -> [
        vsubst [s1,`s:armstate`] t;
        vsubst [s2,`s:armstate`] t;
     ]) @
    [ mk_comb (c_args, s1);
      mk_comb (c_args, s2);
      `read events s1 = e`;
      `read events s2 = e`;
    ])) in

  let postcond = mk_gabs(mk_pair(s1,s2),
    let mr = mk_list (map mk_pair memreads,`:int64#num`) in
    let mw = mk_list (map mk_pair memwrites,`:int64#num`) in
    let e2 = mk_var("e2",`:(armevent)list`) in
    mk_exists(e2,
      list_mk_conj [
        `read PC s1 = returnaddress`;
        `read PC s2 = returnaddress`;
        mk_eq(e2,
            list_mk_comb (f_events,(usedvars @ [`pc:num`;`returnaddress:int64`])));
        `read events s1 = APPEND e2 e`;
        `read events s2 = APPEND e2 e`;
        mk_comb(mk_comb(mk_comb (`memaccess_inbounds`,e2),mr),mw)
      ])) in

  mk_exists(f_events,
    list_mk_forall(fnspec_quants,
      let body = list_mk_icomb "ensures2"
          [`arm`;precond;postcond;
          `\(s:armstate#armstate) (s':armstate#armstate). true`;
          mk_abs(`s:armstate`,mk_small_numeral(numinsts));
          mk_abs(`s:armstate`,mk_small_numeral(numinsts))
          ] in
      if fnspec_globalasms = `true` then body
      else mk_imp(fnspec_globalasms,body)
      ));;

let PROVE_SAFETY_SPEC exec:tactic =
  W (fun (asl,w) ->
    let f_events = fst (dest_exists w) in
    let numinsts =
      let bd = snd(strip_forall(snd(dest_exists w))) in
      let bd = if is_imp bd then snd(dest_imp bd) else bd in
      let _,rs = strip_comb bd in
      let fnstep = last rs in
      dest_small_numeral (snd (dest_abs fnstep)) in

    X_META_EXISTS_TAC f_events THEN
    REWRITE_TAC[C_ARGUMENTS;ALL;NONOVERLAPPING_CLAUSES;fst exec] THEN
    REPEAT GEN_TAC THEN TRY DISCH_TAC THEN
    REPEAT SPLIT_FIRST_CONJ_ASSUM_TAC THEN

    ENSURES2_INIT_TAC "s0" "s0'" THEN
    ARM_N_STUTTER_LEFT_TAC exec (1--numinsts) None THEN
    ARM_N_STUTTER_RIGHT_TAC exec (1--numinsts) "'" None THEN
    REPEAT_N 2 ENSURES_N_FINAL_STATE_TAC THEN
    ASM_REWRITE_TAC[] THEN

    X_META_EXISTS_TAC `e2:(armevent)list` THEN
    CONJ_TAC THENL [MATCH_MP_TAC EQ_SYM THEN UNIFY_REFL_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [
      CONV_TAC (LAND_CONV CONS_TO_APPEND_CONV) THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN UNIFY_REFL_TAC;
      ALL_TAC
    ] THEN
    CONJ_TAC THENL [ REWRITE_TAC[APPEND] THEN NO_TAC; ALL_TAC ] THEN
    (* memaccess_inbounds *)
    REWRITE_TAC[memaccess_inbounds;ALL;EX] THEN
    REPEAT CONJ_TAC THEN
      (REPEAT ((DISJ1_TAC THEN CONTAINED_TAC) ORELSE DISJ2_TAC ORELSE CONTAINED_TAC)));;