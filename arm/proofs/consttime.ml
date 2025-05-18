needs "arm/proofs/equiv.ml";;

(* Find the size of stack access, from specification. This is picked from MAYCHANGE.
   The SP register is expected to have a symbolic variable 'stackpointer' *)
(*
let find_stack_access_size (subroutine_correct_term:term): int option =
  let t = subroutine_correct_term in
  let quants,body = strip_forall t in
  let body = if is_imp body then snd (dest_imp body) else body in
  let e,args = strip_comb body in
  if name_of e <> "ensures" then failwith ("expected ensures, but got " ^ (name_of e)) else
  let maychanges = last args in
  let rec find_stack_size (t:term): int option =
    if is_binary ",," t then
      let a,b = dest_binary ",," maychanges in
      let res = find_stack_size a in
      if res <> None then res else find_stack_size b
    else if is_const t then None
    else if is_comb t then
      let c,arg = dest_comb t in
      if name_of c <> "MAYCHANGE" then None else
      if not (is_list arg) then None else
      let itms = dest_list arg in
      let sizes = List.filter_map (fun (t:term):int option ->
        try
          let a,b = dest_binary ":>" t in
          if name_of a <> "memory" then None else
          let c,d = dest_comb b in
          if name_of c <> "bytes" then None else
          let ptr,sz = dest_pair d in
          let isz = dest_small_numeral sz in
          let ptrbase,ofs = dest_binary "word_sub" ptr in
          if ptrbase = `stackpointer:int64` &&
             ofs = mk_comb (`word:num->int64`,mk_small_numeral isz)
          then (Some isz)
          else None
        with _ -> None)
        itms in
      if sizes = [] then None else Some (hd sizes)
    else None in
  find_stack_size maychanges;;
*)
let find_stack_access_size (subroutine_correct_term:term): int option =
  try
    let t = find_term (fun t -> is_binary "word_sub" t &&
        let a,b = dest_binary "word_sub" t in
        a = mk_var("stackpointer",`:int64`)) subroutine_correct_term in
    let sz = snd (dest_comb t) in
    Some (dest_small_numeral (snd (dest_comb sz)))
  with _ -> None;;

let mk_safety_spec ?(numinstsopt:int option) (fnargs,_,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec =

  let get_c_elemtysize varname =
    let _,s,_ = find (fun name,_,_ -> name = varname) fnargs in
    if String.starts_with ~prefix:"uint64_t" s then 8
    else if String.starts_with ~prefix:"uint8_t" s then 1
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
  let stack_access_size: int option = find_stack_access_size fnspec in
  assert ((readsp = None) = (stack_access_size = None));

  (* memreads/writes without stackpointer *)
  let memreads = map (fun (varname,range) ->
      find (fun t -> name_of t = varname) fnspec_quants,
      mk_small_numeral(int_of_string range * get_c_elemtysize varname))
    (meminputs @ memoutputs @ memtemps) in
  let memwrites = map (fun (varname,range) ->
      find (fun t -> name_of t = varname) fnspec_quants,
      mk_small_numeral(int_of_string range * get_c_elemtysize varname))
    (memoutputs @ memtemps) in

  let usedvars = itlist (fun (t,_) l ->
    let vars = find_terms is_var t in union vars l) (memreads @ memwrites) [] in
  let numinsts = match numinstsopt with
    | Some n -> n
    | None -> Array.length (snd exec) / 4 in

  let f_events_args = usedvars @
    (match stack_access_size with
     | None -> [`pc:num`;`returnaddress:int64`]
     | Some sz ->
       let baseptr = subst [mk_small_numeral sz,`n:num`] `word_sub stackpointer (word n):int64` in
       [`pc:num`;baseptr;`returnaddress:int64`]) in
  let f_events = mk_var("f_events",
    itlist mk_fun_ty (map type_of f_events_args) `:(armevent)list`) in

  let memreads,memwrites =
    match stack_access_size with
    | None -> memreads,memwrites
    | Some sz ->
      let baseptr = subst [mk_small_numeral sz,`n:num`] `word_sub stackpointer (word n):int64` in
      (memreads @ [baseptr,mk_small_numeral sz],
       memwrites @ [baseptr,mk_small_numeral sz]) in

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
        mk_eq(e2, list_mk_comb (f_events,f_events_args));
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
    let quantvars,forall_body = strip_forall(snd(dest_exists w)) in
    let numinsts =
      let bd = forall_body in
      let bd = if is_imp bd then snd(dest_imp bd) else bd in
      let _,rs = strip_comb bd in
      let fnstep = last rs in
      dest_small_numeral (snd (dest_abs fnstep)) in
    let stack_access_size: int option = find_stack_access_size forall_body in

    X_META_EXISTS_TAC f_events THEN
    REWRITE_TAC[C_ARGUMENTS;ALL;ALLPAIRS;NONOVERLAPPING_CLAUSES;fst exec] THEN
    (match stack_access_size with
     | None -> REPEAT GEN_TAC
     | Some sz -> (REPEAT (W (fun (asl,w) ->
        let x,_ = dest_forall w in
        if name_of x = "stackpointer" then NO_TAC else GEN_TAC)) THEN
        WORD_FORALL_OFFSET_TAC sz THEN
        REPEAT GEN_TAC)) THEN
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

let count_nsteps (subroutine_correct_term:term) exec: int =
  let n = ref 0 in
  let successful = ref true in

  let dest_pc_addr =
    let triple = snd (dest_imp (snd (strip_forall subroutine_correct_term))) in
    let _,(sem::pre::post::frame::[]) = strip_comb triple in
    let read_pc_eq = find_term (fun t -> is_eq t && is_read_pc (lhs t)) post in
    snd (dest_eq read_pc_eq) in

  let _ = can prove (subroutine_correct_term,
    REWRITE_TAC[C_ARGUMENTS;ALL;NONOVERLAPPING_CLAUSES;fst exec] THEN
    (* Do not unfold bignum_from_memory, because there should be no pointers stored in
       buffer *)
    REPEAT STRIP_TAC THEN
    ENSURES_INIT_TAC "s0" THEN
    REPEAT (W (fun (asl,w) ->
      match List.find_opt (fun (_,th) ->
          is_eq (concl th) && is_read_pc (lhs (concl th)))
          asl with
      | None -> successful := false; NO_TAC
      | Some (_,read_pc_th) ->
        if rhs (concl read_pc_th) = dest_pc_addr
        then (* Successful! *) NO_TAC
        else (* Proceed *)
          let _ = n := !n + 1 in ARM_SINGLE_STEP_TAC exec ("s" ^ string_of_int !n)))
    THEN
    NO_TAC) in
  if !successful then !n
  else failwith "has a conditional branch depending on input";;