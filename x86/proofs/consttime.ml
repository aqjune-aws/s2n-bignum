(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

needs "common/consttime.ml";;

let mk_safety_spec
    ?(coda_pc_range:(int*int) option) (* when coda is used: (begin, len) *)
    (fnargs,xx,meminputs,memoutputs,memtemps)
    (subroutine_correct_th:thm) exec: term*(term list) =
  let read_sth_eq (f:term->bool):term->bool =
    fun t -> is_eq t && let l = lhs t in is_binary "read" l &&
      let l' = fst (dest_binary "read" l) in f l' in
  gen_mk_safety_spec ?coda_pc_range (fnargs,xx,meminputs,memoutputs,memtemps)
    subroutine_correct_th exec
    (read_sth_eq (fun t -> t = `SP`))
    (can (fun t ->
            let l = fst (dest_eq t) in
            let l' = fst (dest_binary "read" l) in
            let mem,b64_sp = dest_binary ":>" l' in
            let b64,sp = dest_comb b64_sp in
            check (fun () ->
              name_of mem = "memory" && name_of b64 = "bytes64" &&
              name_of sp = "stackpointer") ()));;

let PROVE_SAFETY_SPEC ?(public_vars:term list option) exec:tactic =
  GEN_PROVE_SAFETY_SPEC ?public_vars:public_vars exec
    [BYTES_LOADED_APPEND_CLAUSE]
    X86_SINGLE_STEP_TAC;;
