import equational_theories.Spectrum.Equation1110.ForwardEncoding
import equational_theories.Spectrum.Equation1110.OrderThirteenEncoding
import equational_theories.Spectrum.Equation1110.CycleRepresentatives

open Spectrum.E1110
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def main (args : List String) : IO Unit := do
  let [dir] := args | throw (IO.userError "usage: Export.lean DIRECTORY")
  IO.FS.createDirAll dir
  for i in List.finRange 101 do
    let d := CycleRepresentatives.data13 i
    if (List.finRange 13).all (fun x => decide (d (d x) ≠ x ∨ d x = x)) then
      let f := if i.val = 0 then OrderThirteen.natFormula 13
        else if i.val = 2 then ForwardEncoding.rowChainNat d
        else if i.val = 4 then ForwardEncoding.slackNat d 2
        else if i.val = 6 then ForwardEncoding.slackNat d 3
        else if i.val = 9 then ForwardEncoding.slackNat d 4
        else if i.val = 10 then ForwardEncoding.slackNat d 4
        else if i.val = 13 then ForwardEncoding.slackNat d 5
        else if i.val = 14 then ForwardEncoding.slackNat d 5
        else if i.val = 20 then ForwardEncoding.slackNat d 6
        else if i.val = 21 then ForwardEncoding.slackNat d 6
        else if i.val = 26 then ForwardEncoding.slackNat d 7
        else if i.val = 27 then ForwardEncoding.slackNat d 7
        else if i.val = 37 then ForwardEncoding.slackNat d 8
        else if i.val = 40 then ForwardEncoding.slackNat d 8
        else if i.val = 68 then ForwardEncoding.slackNat d 10
        else if i.val = 72 then ForwardEncoding.slackNat d 10
        else SquareEncoding.fixedNat d
      let out ← IO.FS.Handle.mk s!"{dir}/C{i.val}.cnf" .write
      out.putStrLn s!"p cnf 4394 {f.clauses.size}"
      for c in f.clauses do
        out.putStrLn (String.intercalate " "
          (c.map fun (v,b) => s!"{if b then "" else "-"}{v+1}") ++ " 0")
