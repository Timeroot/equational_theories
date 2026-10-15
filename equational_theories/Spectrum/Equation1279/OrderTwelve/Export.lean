import equational_theories.Spectrum.Equation1279.OrderTwelve.Core

open Spectrum.E1279.OrderTwelve
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "usage: Export.lean DIRECTORY")
  IO.FS.createDirAll dir
  for i in List.finRange 35 do
    let f := natFormula i
    let out ← IO.FS.Handle.mk s!"{dir}/C{(sourceIndex i).val}.cnf" .write
    out.putStrLn s!"p cnf 1728 {f.clauses.size}"
    for c in f.clauses do
      out.putStrLn (String.intercalate " "
        (c.map fun (v,b) => s!"{if b then "" else "-"}{v+1}") ++ " 0")
