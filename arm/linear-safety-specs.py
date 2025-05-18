ls = open("linear-objs.txt", "r").readlines()

for l in ls:
  l = l.split()[0]
  obj = l[l.rfind('/')+1:]
  fn = obj[:-len(".o")]

  print(fn)
  f = open(f"proofs/{fn}.ml", "a")
  f.write(f"""

(* ------------------------------------------------------------------------- *)
(* Constant-time and memory safety proof.                                    *)
(* ------------------------------------------------------------------------- *)

needs "arm/proofs/consttime.ml";;
needs "arm/proofs/subroutine_signatures.ml";;

let full_spec = mk_safety_spec
    (assoc "{fn}" subroutine_signatures)
    {fn.upper()}_SUBROUTINE_CORRECT
    {fn.upper()}_EXEC;;

let {fn.upper()}_SUBROUTINE_SAFE = time prove
 (full_spec,
  PROVE_SAFETY_SPEC {fn.upper()}_EXEC);;
""")
  f.close()
