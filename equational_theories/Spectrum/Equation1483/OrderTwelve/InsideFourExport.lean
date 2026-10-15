import equational_theories.Spectrum.Equation1483.OrderTwelve.InsideFourRows
open Std.Sat Spectrum.E1483.OrderTwelve
set_option maxRecDepth 65536
set_option maxHeartbeats 0
private def emit (dir name : String) (F : CNF Nat) : IO Unit := do
  let out ← IO.FS.Handle.mk s!"{dir}/{name}.cnf" .write
  out.putStrLn s!"p cnf 22464 {F.clauses.size}"
  for c in F.clauses do
    out.putStrLn (String.intercalate " "
      (c.map fun (v,b) => s!"{if b then "" else "-"}{v+1}") ++ " 0")
def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "usage: Export DIRECTORY")
  IO.FS.createDirAll dir
  emit dir "InsideFourRow0" (HeadLexEncoding.toNat 4 true [(0,0,0),(0,1,0),(0,2,0),(0,3,0),(0,4,1),(0,5,2),(0,6,3),(0,7,3),(0,8,3),(0,9,3),(0,10,3),(0,11,3)])
  emit dir "InsideFourRow1" (HeadLexEncoding.toNat 4 true [(0,0,0),(0,1,0),(0,2,0),(0,3,0),(0,4,1),(0,5,2),(0,6,3),(0,7,2),(0,8,3),(0,9,3),(0,10,3),(0,11,3)])
  emit dir "InsideFourRow2" (HeadLexEncoding.toNat 4 true [(0,0,0),(0,1,0),(0,2,0),(0,3,0),(0,4,1),(0,5,2),(0,6,3),(0,7,1),(0,8,1),(0,9,1),(0,10,2),(0,11,2)])
  emit dir "InsideFourRow3" (HeadLexEncoding.toNat 4 true [(0,0,0),(0,1,0),(0,2,0),(0,3,0),(0,4,1),(0,5,2),(0,6,3),(0,7,1),(0,8,2),(0,9,3),(0,10,3),(0,11,3)])
  emit dir "InsideFourRow4" (HeadLexEncoding.toNat 4 true [(0,0,0),(0,1,0),(0,2,0),(0,3,0),(0,4,1),(0,5,2),(0,6,3),(0,7,1),(0,8,2),(0,9,2),(0,10,3),(0,11,3)])
  emit dir "InsideFourSquareOne" (HeadLexEncoding.toNat 4 true [(0,0,1)])
  emit dir "InsideFourHead01" (HeadLexEncoding.toNat 4 true [(0,2,0),(0,3,1)])
  emit dir "InsideFourHead02" (HeadLexEncoding.toNat 4 true [(0,2,0),(0,3,2)])
  emit dir "InsideFourHead11" (HeadLexEncoding.toNat 4 true [(0,2,1),(0,3,1)])
  emit dir "InsideFourHead12" (HeadLexEncoding.toNat 4 true [(0,2,1),(0,3,2)])
  emit dir "InsideFourCoverage" InsideFourRows.coverage
