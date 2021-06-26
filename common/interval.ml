(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Simple interval reasoning tools for expressions involving val/bitval.     *)
(* ========================================================================= *)

let BOUNDER_RULE =
  let is_add = is_binop `( + ):real->real->real`
  and is_sub = is_binop `( - ):real->real->real`
  and is_mul = is_binop `( * ):real->real->real`
  and is_pow = is_binop `( pow ):real->num->real`
  and is_neg =
    let t = `(--):real->real` in
    fun tm -> is_comb tm && rator tm = t
  and is_abs =
    let t = `abs:real->real` in
    fun tm -> is_comb tm && rator tm = t
  and BIRATIONAL_RULE =
    CONV_RULE (BINOP2_CONV (LAND_CONV REAL_RAT_REDUCE_CONV)
                           (RAND_CONV REAL_RAT_REDUCE_CONV)) in
  let rule_val = (PART_MATCH (lhand o rand) o prove)
   (`&0:real <= &(val(w:int64)) /\ &(val w):real <= &18446744073709551615`,
    REWRITE_TAC[REAL_POS] THEN MP_TAC(ISPEC `w:int64` VAL_BOUND) THEN
    REWRITE_TAC[REAL_OF_NUM_LE; DIMINDEX_64] THEN ARITH_TAC)
  and rule_bitval = (PART_MATCH (lhand o rand) o prove)
   (`&0:real <= &(bitval b) /\ &(bitval b):real <= &1`,
    REWRITE_TAC[REAL_OF_NUM_LE; LE_0; BITVAL_BOUND])
  and rule_const tm = let th = SPEC tm REAL_LE_REFL in CONJ th th
  and rule_neg =
    let pth = REAL_ARITH
     `!l u x:real. l <= x /\ x <= u ==> --u <= --x /\ --x <= --l` in
    BIRATIONAL_RULE o MATCH_MP pth
  and rule_abs =
    let pth = REAL_ARITH
     `!l u x:real. l <= x /\ x <= u
                   ==> &0 <= abs x /\ abs(x) <= max (abs l) (abs u)` in
    BIRATIONAL_RULE o MATCH_MP pth
  and rule_add =
    let pth = REAL_ARITH
     `!l1 u1 l2 u2 x y:real.
        (l1 <= x /\ x <= u1) /\
        (l2 <= y /\ y <= u2)
        ==> l1 + l2 <= x + y /\ x + y <= u1 + u2` in
    let rule = MATCH_MP pth in
    fun th1 th2 -> BIRATIONAL_RULE (rule (CONJ th1 th2))
  and rule_sub =
    let pth = REAL_ARITH
     `!l1 u1 l2 u2 x y:real.
        (l1 <= x /\ x <= u1) /\
        (l2 <= y /\ y <= u2)
        ==> l1 - u2 <= x - y /\ x - y <= u1 - l2` in
    let rule = MATCH_MP pth in
    fun th1 th2 -> BIRATIONAL_RULE (rule (CONJ th1 th2))
  and rule_mul =
    let lemma = prove
     (`l:real <= x /\ x <= u
       ==> !a. a * l <= a * x /\ a * x <= a * u \/
               a * u <= a * x /\ a * x <= a * l`,
      MESON_TAC[REAL_LE_NEGTOTAL; REAL_LE_LMUL;
                REAL_ARITH `a * x <= a * y <=> --a * y <= --a * x`]) in
    let pth = prove
      (`!l1 u1 l2 u2 x y:real.
        (l1 <= x /\ x <= u1) /\
        (l2 <= y /\ y <= u2)
        ==> min (l1 * l2) (min (l1 * u2) (min (u1 * l2) (u1 * u2))) <= x * y /\
            x * y <= max (l1 * l2) (max (l1 * u2) (max (u1 * l2) (u1 * u2)))`,
      REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [IMP_CONJ_ALT] THEN
      DISCH_THEN(ASSUME_TAC o SPEC `x:real` o MATCH_MP lemma) THEN
      DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN DISCH_THEN(fun th ->
        MP_TAC(SPEC `l2:real` th) THEN MP_TAC(SPEC `u2:real` th)) THEN
      ASM_REAL_ARITH_TAC) in
    let rule = MATCH_MP pth in
    fun th1 th2 -> BIRATIONAL_RULE (rule (CONJ th1 th2))
  and rule_pow =
    let pth = prove
     (`l:real <= x /\ x <= u
       ==> !n. if EVEN n
               then &0 <= x pow n /\ x pow n <= (max (abs l) (abs u)) pow n
               else l pow n <= x pow n /\ x pow n <= u pow n`,
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
      ASM_SIMP_TAC[REAL_POW_LE2_ODD; GSYM NOT_EVEN] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST1_TAC o
        REWRITE_RULE[EVEN_EXISTS]) THEN
      REWRITE_TAC[GSYM REAL_POW_POW] THEN
      SIMP_TAC[REAL_POW_LE; REAL_LE_POW_2] THEN
      MATCH_MP_TAC REAL_POW_LE2 THEN REWRITE_TAC[REAL_LE_POW_2] THEN
      ASM_REWRITE_TAC[REAL_ABS_ABS; GSYM REAL_LE_SQUARE_ABS] THEN
      ASM_REAL_ARITH_TAC) in
    let rule = MATCH_MP pth
    and cass =
      CONV_RULE(RATOR_CONV (LAND_CONV NUM_EVEN_CONV) THENC
                GEN_REWRITE_CONV I [COND_CLAUSES]) in
    fun th n -> BIRATIONAL_RULE (cass (SPEC n (rule th))) in
  let rec bounder tm =
    if is_ratconst tm then rule_const tm
    else if is_neg tm then rule_neg (bounder(rand tm))
    else if is_abs tm then rule_abs (bounder(rand tm))
    else if is_add tm then rule_add (bounder(lhand tm)) (bounder(rand tm))
    else if is_sub tm then rule_sub (bounder(lhand tm)) (bounder(rand tm))
    else if is_mul tm then rule_mul (bounder(lhand tm)) (bounder(rand tm))
    else if is_pow tm && is_numeral (rand tm) then
        rule_pow (bounder(lhand tm)) (rand tm)
    else try rule_val tm with Failure _ -> try rule_bitval tm
    with Failure _ -> failwith "BOUNDER_RULE: unhandled term" in
  bounder;;

(* ------------------------------------------------------------------------- *)
(* Tactic form of bounder for some common idioms                             *)
(* ------------------------------------------------------------------------- *)

let (BOUNDER_TAC:tactic) =
  let pats =
    map (fun t ->
      can (term_match [] (rand(rand t))),
      (rand o lhand),MATCH_MP_TAC o MATCH_MP (REAL_ARITH t))
    [`l:real <= x /\ x <= r ==> a <= l /\ r <= b ==> a <= x /\ x <= b`;
     `l:real <= x /\ x <= r ==> a <= l /\ r < b ==> a <= x /\ x < b`;
     `l:real <= x /\ x <= r ==> a < l /\ r <= b ==> a < x /\ x <= b`;
     `l:real <= x /\ x <= r ==> a < l /\ r < b ==> a < x /\ x < b`;
     `l:real <= x /\ x <= r ==> abs(l) <= a /\ abs(r) <= a ==> abs(x) <= a`;
     `l:real <= x /\ x <= r ==> abs(l) < a /\ abs(r) < a ==> abs(x) < a`] @
    map (fun t ->
     (fun tm -> can (term_match [] (rand(rand t))) tm && frees(rand tm) = []),
     lhand,MATCH_MP_TAC o MATCH_MP (REAL_ARITH t))
    [`l:real <= x /\ x <= r ==> r < a ==> x < a`;
     `l:real <= x /\ x <= r ==> r <= a ==> x <= a`] @
    map (fun t ->
     (fun tm -> can (term_match [] (rand(rand t))) tm && frees(lhand tm) = []),
     rand,MATCH_MP_TAC o MATCH_MP (REAL_ARITH t))
    [`l:real <= x /\ x <= r ==> a < l ==> a < x`;
     `l:real <= x /\ x <= r ==> a <= l ==> a <= x`] in
  fun (asl,w) ->
    let p,pfn,tac = find (fun (p,pfn,tac) -> p w) pats in
    let t = pfn w in
    let pth = REAL_POLY_CONV t in
    let bth = BOUNDER_RULE(rand(concl pth)) in
    let eth = GEN_REWRITE_RULE
      (fun c -> BINOP2_CONV (RAND_CONV c) (LAND_CONV c)) [SYM pth] bth in
    (tac eth THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Tool to simplify assumptions and possibly prove carries are zero.         *)
(* ------------------------------------------------------------------------- *)

(*** Might be some arguments against saving the restore0 theorem?
 *** It's valid and in principle useful but does slightly change the
 *** fact that the lhs's are variables to eliminate.
 ***)

let DECARRY_RULE =
  let simper1 = MATCH_MP (REAL_ARITH
    `&2 pow 64 * hi + lo:real = z ==> hi = (z - lo) / &2 pow 64`)
  and simper0 = MATCH_MP (REAL_ARITH
    `&2 pow 64 * hi:real = z ==> hi = z / &2 pow 64`)
  and simper3 = MATCH_MP (REAL_ARITH
    `--(&2 pow 64) * hi + lo:real = z ==> hi = (lo - z) / &2 pow 64`)
  and simper2 = MATCH_MP (REAL_ARITH
    `--(&2 pow 64) * hi:real = z ==> hi = --z / &2 pow 64`)
  and uncarry = (MATCH_MP o prove)
   (`&b:real = t /\ (l <= t /\ t <= u)
     ==> u < &1 ==> &b:real = &0`,
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH_RULE `n = 0 <=> n < 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LT] THEN REAL_ARITH_TAC)
  and upcarry = (MATCH_MP o prove)
  (`&(bitval b):real = t /\ (l <= t /\ t <= u)
     ==> &0 < l ==> &(bitval b):real = &1`,
   BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[BITVAL_CLAUSES] THEN
   REAL_ARITH_TAC)
  and restore1 = (MATCH_MP o REAL_ARITH)
   `&2 pow 64 * hi + lo:real = z /\ hi = &0 ==> lo = z`
  and restore0 = (MATCH_MP o REAL_ARITH)
   `&2 pow 64 * hi:real = z /\ hi = &0 ==> z = &0`
  and restore3 = (MATCH_MP o REAL_ARITH)
   `--(&2 pow 64) * hi + lo:real = z /\ hi = &0 ==> lo = z`
  and restore2 = (MATCH_MP o REAL_ARITH)
   `--(&2 pow 64) * hi:real = z /\ hi = &0 ==> z = &0`
  and destore1 = (MATCH_MP o REAL_ARITH)
   `&2 pow 64 * hi + lo:real = z /\ hi = &1 ==> lo = z - &2 pow 64`
  and destore0 = (MATCH_MP o REAL_ARITH)
   `&2 pow 64 * hi:real = z /\ hi = &1 ==> z = &2 pow 64`
  and destore3 = (MATCH_MP o REAL_ARITH)
   `--(&2 pow 64) * hi + lo:real = z /\ hi = &1 ==> lo = z + &2 pow 64`
  and destore2 = (MATCH_MP o REAL_ARITH)
   `--(&2 pow 64) * hi:real = z /\ hi = &1 ==> z = --(&2 pow 64)`
  and bitty = can (term_match [] `&(bitval b):real`) in
  let simper th =
    try simper1 th with Failure _ ->
    try simper0 th with Failure _ ->
    try simper3 th with Failure _ ->
    simper2 th
  and restore th =
    let th' =
      try restore1 th with Failure _ ->
      try restore0 th with Failure _ ->
      try restore3 th with Failure _ ->
      restore2 th in
    let l,r = dest_eq(concl th') in
    if l = r then [] else [th']
  and destore th =
    let th' =
      try destore1 th with Failure _ ->
      try destore0 th with Failure _ ->
      try destore3 th with Failure _ ->
      destore2 th in
    let l,r = dest_eq(concl th') in
    if l = r then [] else [th'] in
  let rec zonker ths =
    match ths with
      [] -> []
    | th::oths ->
          let oths' = zonker oths in
          let th' =
            CONV_RULE (RAND_CONV(PURE_REWRITE_CONV oths' THENC
                                 REAL_POLY_CONV))
                      (simper th) in
          let etm = concl th' in
          let lrth = time BOUNDER_RULE (rand etm) in
          if rat_of_term(rand(rand(concl lrth))) </ num_1 then
            let ith = uncarry (CONJ th' lrth) in
            let bth = REAL_RAT_LT_CONV(lhand(concl ith)) in
            let th'' = MP ith (EQT_ELIM bth) in
            th''::(restore (CONJ th th'') @ oths')
          else if bitty(lhand etm) &&
                  rat_of_term(lhand(lhand(concl lrth))) >/ num_0 then
            let ith = upcarry (CONJ th' lrth) in
            let bth = REAL_RAT_LT_CONV(lhand(concl ith)) in
            let th'' = MP ith (EQT_ELIM bth) in
            th''::(destore (CONJ th th'') @ oths')
          else
            th'::oths' in
  zonker;;

(* ------------------------------------------------------------------------- *)
(* A dual that replaces the sum, but doesn't try to prove any bounds. The    *)
(* idea here is just to collect the "ignored high parts" explicitly.         *)
(* ------------------------------------------------------------------------- *)

let DESUM_RULE =
  let simper1 = MATCH_MP (REAL_ARITH
    `&2 pow 64 * hi + lo:real = z ==> lo = z - &2 pow 64 * hi`)
  and simper0 = MATCH_MP (REAL_ARITH
    `&2 pow 64 * hi:real = z ==> hi = z / &2 pow 64`)
  and simper3 = MATCH_MP (REAL_ARITH
    `--(&2 pow 64) * hi + lo:real = z ==> lo = z + &2 pow 64 * hi`)
  and simper2 = MATCH_MP (REAL_ARITH
    `--(&2 pow 64) * hi:real = z ==> hi = --z / &2 pow 64`) in
  let simper th =
    try simper1 th with Failure _ ->
    try simper0 th with Failure _ ->
    try simper3 th with Failure _ ->
    simper2 th in
  let rec zonker ths =
    match ths with
      [] -> []
    | th::oths ->
          let oths' = zonker oths in
          let th' =
            CONV_RULE (RAND_CONV(PURE_REWRITE_CONV oths' THENC
                                 REAL_POLY_CONV))
                      (simper th) in
          th'::oths' in
  zonker;;

(* ------------------------------------------------------------------------- *)
(* Do something with the "accumulator" assumptions, removing them            *)
(* in the "POP" case, and in both cases applying a few rewrites.             *)
(* ------------------------------------------------------------------------- *)

let ACCUMULATOR_DEFAULT_REWRITE_RULE =
  let REAL_VAL_WORD_MASK_64 = prove
   (`!b. &(val(word_neg(word(bitval b):int64))):real =
         (&2 pow 64 - &1) * &(bitval b)`,
    REWRITE_TAC[REAL_VAL_WORD_MASK; DIMINDEX_64])
  and REAL_VAL_WORD_NOT_64 = prove
   (`!x:int64. &(val(word_not x)) = &2 pow 64 - &1 - &(val x)`,
    REWRITE_TAC[REAL_VAL_WORD_NOT; DIMINDEX_64]) in
  GEN_REWRITE_RULE (RAND_CONV o TOP_DEPTH_CONV)
    [VAL_WORD_BITVAL; VAL_WORD_0; VAL_WORD_1;
     REAL_VAL_WORD_MASK_64; REAL_VAL_WORD_NOT_64];;

let ACCUMULATOR_ASSUM_LIST:(thm list -> tactic) -> tactic =
  let mf1 = can (term_match [] `&2 pow 64 * c + h:real = x`)
  and mf2 = can (term_match [] `--(&2 pow 64) * c + h:real = x`) in
  let mfn th = let t = concl th in mf1 t || mf2 t in
  fun ttac (asl,w) ->
    ttac (map ACCUMULATOR_DEFAULT_REWRITE_RULE
              (filter mfn (map snd asl))) (asl,w);;

let ACCUMULATOR_POP_ASSUM_LIST:(thm list -> tactic) -> tactic =
  let mf1 = can (term_match [] `&2 pow 64 * c + h:real = x`)
  and mf2 = can (term_match [] `--(&2 pow 64) * c + h:real = x`) in
  let mfn th = let t = concl th in mf1 t || mf2 t in
  fun ttac ->
   POP_ASSUM_LIST
    (fun ths -> let ths1,ths2 = partition mfn ths in
                MAP_EVERY ASSUME_TAC (rev ths2) THEN
                ttac (map ACCUMULATOR_DEFAULT_REWRITE_RULE ths1));;

(* ------------------------------------------------------------------------- *)
(* A beefed-up but very naive ARITH_RULE that also pulls in the              *)
(* knowledge of the bounds of subterms "val n" and "bitval b".               *)
(* ------------------------------------------------------------------------- *)

let VAL_ARITH_RULE =
  let init_conv =
    DEPTH_CONV(GEN_REWRITE_CONV I [BITVAL_CLAUSES] ORELSEC
               WORD_RED_CONV ORELSEC
               NUM_RED_CONV)
  and is_bit t = match t with
      Comb(Const("bitval",_),_) -> true | _ -> false
  and is_val t = match t with
      Comb(Const("val",_),_) -> true | _ -> false
  and bth_val t =
    CONV_RULE (RAND_CONV(TRY_CONV(!word_POW2SIZE_CONV)))
              (PART_MATCH lhand VAL_BOUND t)
  and bth_bit = PART_MATCH lhand BITVAL_BOUND in
  fun tm ->
    let ith = init_conv tm in
    let tm' = rand(concl ith) in
    let btms = find_terms is_bit tm'
    and vtms = find_terms is_val tm' in
    let bths = map bth_bit btms @ map bth_val vtms in
    let atm = itlist (curry mk_imp o concl) bths tm' in
    let ath = ARITH_RULE atm in
    EQ_MP (SYM ith) (rev_itlist (C MP) bths ath);;

(* ------------------------------------------------------------------------- *)
(* Accumulation tactic, useful for reasoning about carry chains.             *)
(* - reduce val(word n) for particular n                                     *)
(* - express everything in a sign-natural way over R.                        *)
(* - keyed to a specific state                                               *)
(* - tries to work in a unified way for ARM and x86, both carry flags        *)
(* - secondary triggering from zero flag if result is not written (ARM xzr)  *)
(* - includes a similar accumulation for "extr" with a zero register.        *)
(* - ditto word_ushr and word_ushl (which are effectively the same)          *)
(* - the X version excludes writes to certain registers (components)         *)
(* ------------------------------------------------------------------------- *)

let ACCUMULATEX_ARITH_TAC =
  let int64_ty = `:int64`
  and patfn = can (term_match [] `read Xnn s = e`)
  and pth_zerotrig = prove
   (`(read ZZ s <=> val(a:int64) = 0) ==> read (rvalue a) s = a`,
    REWRITE_TAC[READ_RVALUE])
  and pth_adc = prove
   (`!(s:S) Xnn (x:int64) y b.
        read Xnn s = word_add (word_add x y) (word(bitval b))
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val y) + &(bitval b) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val y + bitval b) <=> c) /\
                  ((val x + val y + bitval b < 2 EXP 64) <=> ~c)`,
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD;
                REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`2 EXP 64 <= val(x:int64) + val(y:int64) + bitval b`;
      `word_add (word_add x y) (word(bitval b)):int64`] THEN
    ASM_REWRITE_TAC[GSYM ACCUMULATE_ADC; VAL_WORD_BITVAL; NOT_LE])
  and pth_sbc = prove
   (`!(s:S) Xnn (x:int64) y b.
        read Xnn s = word_sub x (word_add y (word(bitval b)))
        ==> ?c z. (--(&2 pow 64) * &(bitval c) + &(val z):real =
                   &(val x) - &(val y) - &(bitval b) /\
                   read Xnn s = z) /\
                  (val x < val y + bitval b <=> c) /\
                  (val y + bitval b <= val x <=> ~c)`,
    REWRITE_TAC[REAL_ARITH `--e * c + z:real = x - y - b <=>
                            e * c + x = y + b + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD;
                REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`val(x:int64) < val(y:int64) + bitval b`;
      `word_sub x (word_add y (word(bitval b))):int64`] THEN
    ASM_REWRITE_TAC[ACCUMULATE_SBB; NOT_LT] THEN ARITH_TAC)
  and pth_sub = prove
   (`!(s:S) Xnn x y:int64.
        read Xnn s = word_sub x y
        ==> ?c z. (--(&2 pow 64) * &(bitval c) + &(val z):real =
                   &(val x) - &(val y) /\
                   read Xnn s = z) /\
                  (val x < val y <=> c) /\
                  (val y <= val x <=> ~c)`,
    REWRITE_TAC[REAL_ARITH `--e * c + z:real = x - y <=>
                            e * c + x = y + z`] THEN
    REWRITE_TAC[REAL_OF_NUM_POW; REAL_OF_NUM_ADD;
                REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
    REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`val(x:int64) < val(y:int64)`;
      `word_sub x y:int64`] THEN
    ASM_REWRITE_TAC[ACCUMULATE_SUB; NOT_LT] THEN ARITH_TAC)
  and pth_mul_hi = prove
   (`!(s:S) Xnn (x:int64) (y:int64).
       read Xnn s :int64 =
       word_zx (word_ushr (word (val x * val y):int128)
               (dimindex (:64)))
        ==> ?(h:int64) (l:int64).
               (&2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y) /\
                read Xnn s = h) /\
               word_zx(word(val x * val y):int128):int64 = l`,
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MESON_TAC[ACCUMULATE_MUL])
  and pth_mul_lo = prove
   (`!(s:S) Xnn (x:int64) (y:int64).
       read Xnn s :int64 = word_zx(word(val x * val y):int128)
        ==> ?(h:int64) (l:int64).
               (&2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y) /\
                read Xnn s = l) /\
               word_zx (word_ushr (word (val x * val y):int128)
                       (dimindex (:64))) = h`,
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MESON_TAC[ACCUMULATE_MUL])
  and pth_mul_hi2 = prove
   (`!(s:S) Xnn (x:int64) (y:int64).
        read Xnn s :int64 =
        word((val x * val y) DIV 2 EXP dimindex(:64))
        ==> ?(h:int64) (l:int64).
               (&2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y) /\
                read Xnn s = h) /\
               (word(0 + val x * val y) = l /\
                word(val x * val y) = l)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN
    GEN_REWRITE_TAC (RAND_CONV o TOP_DEPTH_CONV) [WORD_MUL; WORD_VAL] THEN
    REWRITE_TAC[WORD_MULTIPLICATION_LOHI] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MESON_TAC[ACCUMULATE_MUL])
  and pth_mul_lo2 = prove
   (`!(s:S) Xnn (x:int64) (y:int64).
        read Xnn s :int64 = word(0 + val x * val y)
        ==> ?(h:int64) (l:int64).
               (&2 pow 64 * &(val h) + &(val l):real = &(val x) * &(val y) /\
                read Xnn s = l) /\
               (word((val x * val y) DIV 2 EXP dimindex(:64)) = h /\
                word(val x * val y) = l)`,
    REWRITE_TAC[ADD_CLAUSES; WORD_MUL; WORD_VAL] THEN
    REWRITE_TAC[WORD_MULTIPLICATION_LOHI] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MESON_TAC[ACCUMULATE_MUL])
  and pth_ushr = prove
   (`!(s:S) Xnn (x:int64) k.
          read Xnn s = word_ushr x k
          ==> k < 64
              ==> ?(h:int64) (l:int64).
                      (&2 pow 64 * &(val h) + &(val l):real =
                        &2 pow (64 - k) * &(val x) /\
                       read Xnn s = h) /\
                      word_shl x (64 - k) = l /\
                      word_subword (word_join x (word 0:int64):int128)
                                   (k MOD dimindex (:64),
                                    dimindex (:64)) = l`,
    REPEAT STRIP_TAC THEN EXISTS_TAC `read (Xnn:(S,int64)component) s` THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    ASM_REWRITE_TAC[UNWIND_THM1; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT; WORD_SUBWORD_JOIN_AS_SHL; LT_IMP_LE] THEN
    REWRITE_TAC[GSYM VAL_EQ; VAL_WORD_USHR; VAL_WORD_SHL; DIMINDEX_64] THEN
    REWRITE_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC(MESON[DIVISION_SIMP]
     `x = n * y DIV n ==> x + y MOD n = y`) THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `2 EXP 64 = 2 EXP (64 - k) * 2 EXP k` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      SIMP_TAC[DIV_MULT2; EXP_EQ_0; ARITH_EQ]]) in
  let pth_extr = prove
   (`!(s:S) Xnn (x:int64) k.
          read Xnn s = word_subword (word_join (word 0:int64) x :int128)
                                    (k MOD dimindex (:64),dimindex (:64))
          ==> k < 64
              ==> ?(h:int64) (l:int64).
                      (&2 pow 64 * &(val h) + &(val l):real =
                        &2 pow (64 - k) * &(val x) /\
                       read Xnn s = h) /\
                      word_shl x (64 - k) = l /\
                      word_subword (word_join x (word 0:int64):int128)
                                   (k MOD dimindex (:64),
                                    dimindex (:64)) = l`,
    REPEAT GEN_TAC THEN REWRITE_TAC[IMP_IMP] THEN STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] pth_ushr) THEN
    ASM_SIMP_TAC[DIMINDEX_64; MOD_LT; WORD_SUBWORD_JOIN_AS_USHR; LT_IMP_LE])
  and pth_mul_hil = prove
   (`!(s:S) Xnn n (y:int64).
        read Xnn s :int64 =
        word_zx (word_ushr (word (NUMERAL n * val y):int128)
                (dimindex (:64)))
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                   (&2 pow 64 * &(val h) + &(val l):real =
                    &(NUMERAL n) * &(val y) /\
                    read Xnn s = h) /\
                   word_zx(word(NUMERAL n * val y):int128):int64 = l`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `word(NUMERAL n):int64`; `y:int64`]
          pth_mul_hi) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_lol = prove
     (`!(s:S) Xnn n (y:int64).
         read Xnn s :int64 = word_zx(word(NUMERAL n * val y):int128)
          ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                   (&2 pow 64 * &(val h) + &(val l):real =
                    &(NUMERAL n) * &(val y) /\
                    read Xnn s = l) /\
                   word_zx (word_ushr (word (NUMERAL n * val y):int128)
                           (dimindex (:64))) = h`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `word(NUMERAL n):int64`; `y:int64`]
          pth_mul_lo) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_hir = prove
   (`!(s:S) Xnn (x:int64) n.
        read Xnn s :int64 =
        word_zx (word_ushr (word (val x * NUMERAL n):int128)
                (dimindex (:64)))
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                   (&2 pow 64 * &(val h) + &(val l):real =
                    &(val x) * &(NUMERAL n) /\
                    read Xnn s = h) /\
                   word_zx(word(val x * NUMERAL n):int128):int64 = l`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `x:int64`; `word(NUMERAL n):int64`]
          pth_mul_hi) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_lor = prove
     (`!(s:S) Xnn (x:int64) n.
         read Xnn s :int64 = word_zx(word(val x * NUMERAL n):int128)
          ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                   (&2 pow 64 * &(val h) + &(val l):real =
                    &(val x) * &(NUMERAL n) /\
                    read Xnn s = l) /\
                   word_zx (word_ushr (word (val x * NUMERAL n):int128)
                           (dimindex (:64))) = h`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `x:int64`; `word(NUMERAL n):int64`]
          pth_mul_lo) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_hil2 = prove
   (`!(s:S) Xnn n (y:int64).
        read Xnn s :int64 =
        word((NUMERAL n * val y) DIV 2 EXP dimindex(:64))
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                     (&2 pow 64 * &(val h) + &(val l):real =
                      &(NUMERAL n) * &(val y) /\
                      read Xnn s = h) /\
                     (word(0 + NUMERAL n * val y) = l /\
                      word(NUMERAL n * val y) = l)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `word(NUMERAL n):int64`; `y:int64`]
          pth_mul_hi2) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_lol2 = prove
   (`!(s:S) Xnn n (y:int64).
        read Xnn s :int64 = word(0 + NUMERAL n * val y)
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                     (&2 pow 64 * &(val h) + &(val l):real =
                      &(NUMERAL n) * &(val y) /\
                      read Xnn s = l) /\
                     (word((NUMERAL n * val y) DIV 2 EXP dimindex(:64)) = h /\
                      word(NUMERAL n * val y) = l /\
                      word((val(word(NUMERAL n):int64) * val y)
                           DIV 2 EXP dimindex(:64)) = h /\
                      word(val(word(NUMERAL n):int64) * val y) = l)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `word(NUMERAL n):int64`; `y:int64`]
          pth_mul_lo2) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN MESON_TAC[])
  and pth_mul_hir2 = prove
   (`!(s:S) Xnn (x:int64) n.
        read Xnn s :int64 =
        word((val x * NUMERAL n) DIV 2 EXP dimindex(:64))
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                     (&2 pow 64 * &(val h) + &(val l):real =
                      &(val x) * &(NUMERAL n) /\
                      read Xnn s = h) /\
                     (word(0 + val x * NUMERAL n) = l /\
                      word(val x * NUMERAL n) = l)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `x:int64`; `word(NUMERAL n):int64`]
          pth_mul_hi2) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT])
  and pth_mul_lor2 = prove
   (`!(s:S) Xnn (x:int64) n.
        read Xnn s :int64 = word(0 + val x * NUMERAL n)
        ==> NUMERAL n < 2 EXP 64
            ==> ?(h:int64) (l:int64).
                    (&2 pow 64 * &(val h) + &(val l):real =
                     &(val x) * &(NUMERAL n) /\
                     read Xnn s = l) /\
                    (word((val x * NUMERAL n) DIV 2 EXP dimindex(:64)) = h /\
                     word(val x * NUMERAL n) = l /\
                     word((val x * val(word(NUMERAL n):int64)) DIV
                          2 EXP dimindex(:64)) = h /\
                     word(val x * val(word(NUMERAL n):int64)) = l)`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`s:S`; `Xnn:(S,int64)component`;
                   `x:int64`; `word(NUMERAL n):int64`]
          pth_mul_lo2) THEN
    FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[VAL_WORD; DIMINDEX_64] THEN
    ASM_SIMP_TAC[MOD_LT] THEN MESON_TAC[])
  and pth_sbc_rn = prove
   (`!(s:S) Xnn (x:int64) n b.
        read Xnn s = word_sub x (word(n + bitval b))
        ==> ?c z. (--(&2 pow 64) * &(bitval c) + &(val z):real =
                   &(val x) - &(val(word n:int64)) - &(bitval b) /\
                   read Xnn s = z) /\
                  (val x < val(word n:int64) + bitval b <=> c) /\
                  (val(word n:int64) + bitval b <= val x <=> ~c)`,
    MP_TAC pth_sbc THEN
    REPLICATE_TAC 3 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th ->
    X_GEN_TAC `n:num` THEN MP_TAC(SPEC `word n:int64` th)) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    REWRITE_TAC[WORD_ADD] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; ADD_ASSOC])
  and pth_adc_c0 = prove
   (`!(s:S) Xnn (x:int64) y.
        read Xnn s = word_add (word_add x y) (word 0)
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val y) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val y + 0 <=> c) /\
                   (val x + val y + 0 < 2 EXP 64 <=> ~c) /\
                   (2 EXP 64 <= val x + val y + 0 <=> c) /\
                   (val x + val y + 0 < 2 EXP 64 <=> ~c))`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 4 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `F`) THEN
    REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; REAL_ADD_LID; NOT_LE] THEN
    REWRITE_TAC[ADD_CLAUSES; BITVAL_CLAUSES; WORD_ADD_0; REAL_ADD_RID] THEN
    REWRITE_TAC[CONJ_ACI])
  and pth_add_r0 = prove
   (`!(s:S) Xnn (x:int64) b.
        read Xnn s = word_add x (word(bitval b))
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(bitval b) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + bitval b) <=> c) /\
                  ((2 EXP 64 <= val x + 0 + bitval b) <=> c) /\
                  ((2 EXP 64 <= 0 + val x + bitval b) <=> c) /\
                  ((val x + bitval b < 2 EXP 64) <=> ~c) /\
                  ((val x + 0 + bitval b < 2 EXP 64) <=> ~c) /\
                  ((0 + val x + bitval b < 2 EXP 64) <=> ~c)`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 3 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `word 0:int64`) THEN
    REWRITE_TAC[WORD_ADD_0; VAL_WORD_0; REAL_ADD_LID; NOT_LE] THEN
    REWRITE_TAC[ADD_CLAUSES; CONJ_ACI])
  and pth_adc_c1 = prove
   (`!(s:S) Xnn (x:int64) y.
        read Xnn s = word_add (word_add x y) (word 1)
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val y) + &1 /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val y + 1 <=> c) /\
                   (val x + val y + 1 < 2 EXP 64 <=> ~c))`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 4 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `T`) THEN
    REWRITE_TAC[VAL_WORD_1; BITVAL_CLAUSES])
  and pth_adc_rn = prove
   (`!(s:S) Xnn (x:int64) n b.
        read Xnn s = word_add x (word(n + bitval b))
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val(word n:int64)) + &(bitval b) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val(word n:int64) + bitval b) <=> c) /\
                  ((val x + val(word n:int64) + bitval b < 2 EXP 64) <=> ~c)`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 3 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(fun th ->
    X_GEN_TAC `n:num` THEN MP_TAC(SPEC `word n:int64` th)) THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    REWRITE_TAC[WORD_ADD] THEN
    REWRITE_TAC[GSYM WORD_ADD_ASSOC; ADD_ASSOC])
  and pth_add = prove
   (`!(s:S) Xnn (x:int64) y.
        read Xnn s = word_add x y
        ==> ?c z. (&2 pow 64 * &(bitval c) + &(val z):real =
                   &(val x) + &(val y) /\
                   read Xnn s = z) /\
                  ((2 EXP 64 <= val x + val y) <=> c) /\
                  ((val x + val y < 2 EXP 64) <=> ~c)`,
    MP_TAC pth_adc THEN
    REPLICATE_TAC 4 (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `F`) THEN
    REWRITE_TAC[BITVAL_CLAUSES; ADD_CLAUSES; REAL_ADD_RID; WORD_ADD_0]) in
  let MATCH_MTH_TAC th =
    let th' = try MATCH_MP pth_mul_hi th with Failure _ ->
              try MATCH_MP pth_mul_lo th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_NTH_TAC th =
    let th' = try MATCH_MP pth_mul_hi2 th with Failure _ ->
              try MATCH_MP pth_mul_lo2 th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_LTH_TAC th =
    let th' = try MATCH_MP pth_mul_hil th with Failure _ ->
              try MATCH_MP pth_mul_hir th with Failure _ ->
              try MATCH_MP pth_mul_lol th with Failure _ ->
              try MATCH_MP pth_mul_lor th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_KTH_TAC th =
    let th' = try MATCH_MP pth_mul_hil2 th with Failure _ ->
              try MATCH_MP pth_mul_hir2 th with Failure _ ->
              try MATCH_MP pth_mul_lol2 th with Failure _ ->
              try MATCH_MP pth_mul_lor2 th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_ETH_TAC th =
    let th' = try MATCH_MP pth_extr th with Failure _ ->
              try MATCH_MP pth_ushr th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th'
  and MATCH_PTH_TAC th =
    let th' = try MATCH_MP pth_adc th with Failure _ ->
              try MATCH_MP pth_adc_rn th with Failure _ ->
              try MATCH_MP pth_adc_c1 th with Failure _ ->
              try MATCH_MP pth_adc_c0 th with Failure _ ->
              try MATCH_MP pth_add_r0 th with Failure _ ->
              try MATCH_MP pth_sbc th with Failure _ ->
              try MATCH_MP pth_sbc_rn th with Failure _ ->
              try MATCH_MP pth_add th with Failure _ ->
              try MATCH_MP pth_sub th with Failure _ ->
              failwith "No matching accum theorem" in
    MP_TAC th' in
  fun excls ->
    let filterpred t =
      match t with
        Comb(Comb(Const("=",_),Comb(Comb(Const("read",_),c),_)),_) ->
          mem c excls
      | _ -> false in
  fun s ->
    let matchfn t =
      patfn t &&
      let sv = rand(lhand t) in is_var sv && fst(dest_var sv) = s in
    FIRST_X_ASSUM(fun sth ->
     if filterpred(concl sth) then failwith "" else
     ((fun gl -> ((MATCH_MTH_TAC o check (matchfn o concl)) sth THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))) gl) ORELSE

      (fun gl -> ((MATCH_NTH_TAC o check (matchfn o concl)) sth THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN
          (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) gl) ORELSE

      (fun gl -> ((MATCH_LTH_TAC o check (matchfn o concl)) sth THEN
       ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))) gl) ORELSE

      (fun gl -> ((MATCH_KTH_TAC o check (matchfn o concl)) sth THEN
       ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN
          (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) gl) ORELSE

      (fun gl -> ((MATCH_ETH_TAC o check (matchfn o concl)) sth THEN
       ANTS_TAC THENL [CONV_TAC NUM_REDUCE_CONV THEN NO_TAC; ALL_TAC] THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("mulhi_"^s,int64_ty))
        (X_CHOOSE_THEN (mk_var("mullo_"^s,int64_ty)) MP_TAC)) THEN
       CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV NUM_SUB_CONV)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN
          (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th)))) gl) ORELSE

      (fun gl -> ((MATCH_PTH_TAC o check (matchfn o concl)) sth THEN
       CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_VAL_CONV)) THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("carry_"^s,bool_ty))
        (X_CHOOSE_THEN (mk_var("sum_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))) gl) ORELSE

      (fun gl -> ((MATCH_PTH_TAC o
          MATCH_MP pth_zerotrig o check (matchfn o concl)) sth THEN
       CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV WORD_VAL_CONV)) THEN
       DISCH_THEN(X_CHOOSE_THEN (mk_var("carry_"^s,bool_ty))
        (X_CHOOSE_THEN (mk_var("sum_"^s,int64_ty)) MP_TAC)) THEN
       DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (REPEAT_TCL CONJUNCTS_THEN SUBST_ALL_TAC))) gl)));;

let ACCUMULATE_ARITH_TAC = ACCUMULATEX_ARITH_TAC [];;