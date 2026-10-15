import equational_theories.Spectrum.Equation467.OrderTwelve.Encoding
import equational_theories.Spectrum.Equation1110.CycleRepresentatives
open Std.Sat Spectrum.E467 Spectrum.E1110
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "usage: Export.lean DIRECTORY")
  IO.FS.createDirAll dir
  for i in List.finRange 77 do
    let d := CycleRepresentatives.representative12 i
    if (List.finRange 12).all (fun x => decide ((d (d x) ≠ x ∨ d x = x) ∧
        (d (d (d x)) ≠ x ∨ d x = x))) then
      let support := ((List.finRange 12).filter (fun x => d x != x)).foldl
        (fun k x => max k (x.val+1)) 0
      let F := FixedEncoding.natFormula d (max 1 (support-2))
      let out ← IO.FS.Handle.mk s!"{dir}/C{i.val}.cnf" .write
      out.putStrLn s!"p cnf 1728 {F.clauses.size}"
      for c in F.clauses do
        out.putStrLn (String.intercalate " "
          (c.map fun (v,b) => s!"{if b then "" else "-"}{v+1}") ++ " 0")
