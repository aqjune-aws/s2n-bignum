import sys

l = sys.argv[1]

obj = l[l.rfind('/')+1:]
fn = obj[:-len(".o")]

print(fn)
f = open(f"proofs/{fn}.ml", "r")
lines = f.readlines()
f.close()

# If lines contain previous Constant-time blah, remove them.
lines_new = []
for line in lines:
  if line.strip() == "(* Constant-time and memory safety proof.                                    *)" or \
     line.strip() == "(* Constant-time and memory safety proof (nonlinear).                        *)":
    lines_new.pop()
    while lines_new[-1].strip() == "":
      lines_new.pop()
    break
  else:
    lines_new.append(line)

f = open(f"proofs/{fn}.ml", "w")
f.write("".join(lines_new))
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