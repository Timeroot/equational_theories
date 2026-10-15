import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding

/-! Export the exact formulas checked by the rank-three certificates. -/
open Std.Sat Spectrum.E1483.OrderTwelve.RankThree
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def main (args : List String) : IO Unit := do
  let dir := args.headD ".cache/e1483-rank3-export"
  IO.FS.createDirAll dir
  let cases : List (String × List Nat) := caseData ++ [("Coverage",[])]
  for (tag,us) in cases do
    let F := if tag = "Coverage" then coverage else branch us
    let out ← IO.FS.Handle.mk s!"{dir}/{tag}.cnf" .write
    out.putStrLn s!"p cnf 24192 {F.clauses.size}"
    for c in F.clauses do
      out.putStrLn (String.intercalate " "
        (c.map fun (v,b) => s!"{if b then "" else "-"}{v+1}") ++ " 0")
