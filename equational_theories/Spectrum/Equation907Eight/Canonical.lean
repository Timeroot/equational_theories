import equational_theories.Spectrum.Equation907
import Mathlib.Data.Fintype.Perm

namespace Spectrum.E907Eight.Canonical

def cycles (f : Fin 8 → Fin 8) : ℕ → List (Fin 8) → List (List (Fin 8))
  | 0, _ => []
  | _+1, [] => []
  | fuel+1, a::rest =>
    let orbit := a :: ((List.range 7).map (fun j => (f^[j+1]) a)).takeWhile (fun b => b != a)
    orbit :: cycles f fuel (rest.filter (fun b => !(orbit.contains b)))

def order (f : Fin 8 → Fin 8) : List (Fin 8) :=
  match cycles f 8 (List.finRange 8) with
  | [] => []
  | a::rest => a ++ ((rest.mergeSort (fun a b => a.length ≥ b.length)).flatten)

def relabel (f : Fin 8 → Fin 8) : Equiv.Perm (Fin 8) :=
  let table := ((List.finRange 8).map f).toArray
  let cached : Fin 8 → Fin 8 := fun x => table[x.val]!
  ((List.finRange 8).zip (order cached)).foldl
    (fun r ab => r.trans (Equiv.swap ab.1 (r ab.2))) (Equiv.refl _)

def rows : List (Fin 8 → Fin 8) := [
  ![0,2,3,4,5,6,7,1],
  ![0,2,3,4,5,6,1,7],
  ![0,2,3,4,5,1,7,6],
  ![0,2,3,4,5,1,6,7],
  ![0,2,3,4,1,6,7,5],
  ![0,2,3,4,1,6,5,7],
  ![0,2,3,4,1,5,6,7],
  ![0,2,3,1,5,6,4,7],
  ![0,2,3,1,5,4,7,6],
  ![0,2,3,1,5,4,6,7],
  ![0,2,3,1,4,5,6,7],
  ![0,2,1,4,3,6,5,7],
  ![0,2,1,4,3,5,6,7],
  ![0,2,1,3,4,5,6,7],
  ![0,1,2,3,4,5,6,7],
  ![1,0,3,4,5,6,7,2],
  ![1,0,3,4,5,6,2,7],
  ![1,0,3,4,5,2,7,6],
  ![1,0,3,4,5,2,6,7],
  ![1,0,3,4,2,6,7,5],
  ![1,0,3,4,2,6,5,7],
  ![1,0,3,4,2,5,6,7],
  ![1,0,3,2,5,4,7,6],
  ![1,0,3,2,5,4,6,7],
  ![1,0,3,2,4,5,6,7],
  ![1,0,2,3,4,5,6,7],
  ![1,2,0,4,5,6,7,3],
  ![1,2,0,4,5,6,3,7],
  ![1,2,0,4,5,3,7,6],
  ![1,2,0,4,5,3,6,7],
  ![1,2,0,4,3,6,5,7],
  ![1,2,0,4,3,5,6,7],
  ![1,2,0,3,4,5,6,7],
  ![1,2,3,0,5,6,7,4],
  ![1,2,3,0,5,6,4,7],
  ![1,2,3,0,5,4,7,6],
  ![1,2,3,0,5,4,6,7],
  ![1,2,3,0,4,5,6,7],
  ![1,2,3,4,0,6,7,5],
  ![1,2,3,4,0,6,5,7],
  ![1,2,3,4,0,5,6,7],
  ![1,2,3,4,5,0,7,6],
  ![1,2,3,4,5,0,6,7],
  ![1,2,3,4,5,6,0,7],
  ![1,2,3,4,5,6,7,0]]

def rowTables : List (List (Fin 8)) := rows.map (fun g => (List.finRange 8).map g)

def correct (f : Equiv.Perm (Fin 8)) : Bool :=
  let r := relabel f
  let table := (List.finRange 8).map (fun x => r (f (r.symm x)))
  decide (r 0 = 0) && rowTables.contains table

@[spectrum_native]
theorem checked : (permsOfList (List.finRange 8)).all correct = true := by
  native_decide
spectrum_assert checked complete

end Spectrum.E907Eight.Canonical
