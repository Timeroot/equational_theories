import Lean.Elab.Tactic.BVDecide
import Std.Sat.CNF
open Std.Sat Std.Tactic.BVDecide.LRAT Lean.Elab.Tactic.BVDecide.LRAT

def readCNF (file : String) : IO (CNF Nat) := do
  let text ← IO.FS.readFile file
  let mut clauses := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "p " || line.startsWith "c " || line.isEmpty then continue
    let mut clause := []
    for word in line.splitOn " " do
      if word.isEmpty then continue
      let some z := word.toInt? | throw (IO.userError "invalid literal")
      if z == 0 then break
      clause := clause ++ [(z.natAbs - 1, decide (z > 0))]
    clauses := clauses.push clause
  return ⟨clauses⟩

def main (args : List String) : IO Unit := do
  for base in args do
    let cnf ← readCNF (base ++ ".cnf")
    let proof ← loadLRATProof (base ++ ".lrat")
    let trimmed ← IO.ofExcept (trim proof)
    unless check trimmed cnf do throw (IO.userError ("LRAT check failed: " ++ base))
    dumpLRATProof (base ++ ".trimmed.lrat") trimmed false
    IO.println s!"VERIFIED {base}: {trimmed.size} trimmed proof steps"
