import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
open Std.Sat Spectrum.E1076.OrderTwelve
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "usage: Export.lean DIRECTORY")
  IO.FS.createDirAll dir
  let formulas : List (String × CNF Nat) := [
    ("C0", PointEncoding.natFormula (CanonicalData.row (CanonicalData.representative 0)) false),
    ("C1G234", PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 1)) false [2,3,4]),
    ("C2G234", PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 2)) false [2,3,4]),
    ("C3G2345", PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 3)) true [2,3,4,5]),
    ("C4G23456", PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 4)) true [2,3,4,5,6]),
    ("C5G234", PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [2,3,4]),
    ("C5G567", PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [5,6,7]),
    ("C5G891011", PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [8,9,10,11]),
    ("Coverage", RowTransfer.coverage)]
  for (tag,F) in formulas do
    let out ← IO.FS.Handle.mk s!"{dir}/{tag}.cnf" .write
    out.putStrLn s!"p cnf 3456 {F.clauses.size}"
    for c in F.clauses do
      out.putStrLn (String.intercalate " "
        (c.map fun (v,b) => s!"{if b then "" else "-"}{v+1}") ++ " 0")
