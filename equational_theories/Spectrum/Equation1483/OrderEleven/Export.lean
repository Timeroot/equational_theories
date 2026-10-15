import equational_theories.Spectrum.Equation1483.OrderEleven.ImageEncoding

/-! Export the exact Lean CNFs for comparison with the independent generator. -/
open Std.Sat Spectrum.E1483.OrderEleven.ImageEncoding
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "usage: Export.lean DIRECTORY")
  IO.FS.createDirAll dir
  let cases : List (Nat × Bool) := [(2,false),(3,false)] ++
    (List.range 7).flatMap (fun i => [(i+4,false),(i+4,true)])
  for (k,z) in cases do
    let f := smallNat k z
    let file := s!"{dir}/Rank{k}{if z then "Inside" else "Outside"}.cnf"
    let out ← IO.FS.Handle.mk file .write
    out.putStrLn s!"p cnf 14641 {f.clauses.size}"
    for c in f.clauses do
      out.putStrLn (String.intercalate " "
        (c.map fun (v,b) => s!"{if b then "" else "-"}{v+1}") ++ " 0")
