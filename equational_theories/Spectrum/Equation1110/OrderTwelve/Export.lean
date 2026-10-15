import equational_theories.Spectrum.Equation1110.SquareEncoding
import equational_theories.Spectrum.Equation1110.CycleRepresentatives
import equational_theories.Spectrum.Equation1110.OrderThirteenEncoding
import equational_theories.Spectrum.Equation1110.ForwardEncoding
open Std.Sat Spectrum.E1110
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "usage: Export.lean DIRECTORY")
  IO.FS.createDirAll dir
  for i in List.finRange 77 do
    let d := CycleRepresentatives.data12 i
    if (List.finRange 12).all (fun x => decide (d x = x ∨ d (d x) ≠ x)) then
      let F := if i.val = 0 then OrderThirteen.natFormula 12
        else if i.val = 2 then ForwardEncoding.rowChainNat d
        else if i.val = 4 then ForwardEncoding.slackNat d 2
        else if i.val = 6 then ForwardEncoding.slackNat d 3
        else if i.val = 9 then ForwardEncoding.slackNat d 4
        else if i.val = 20 then ForwardEncoding.slackNat d 6 else SquareEncoding.fixedNat d
      let out ← IO.FS.Handle.mk s!"{dir}/C{i.val}.cnf" .write
      out.putStrLn s!"p cnf 3456 {F.clauses.size}"
      for c in F.clauses do
        out.putStrLn (String.intercalate " "
          (c.map fun (v,b) => s!"{if b then "" else "-"}{v+1}") ++ " 0")
