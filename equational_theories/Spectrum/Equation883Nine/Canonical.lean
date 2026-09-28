import equational_theories.Spectrum.Equation883Nine.Normalization
import Mathlib.Data.Fintype.Perm

namespace Spectrum.E883Nine.Canonical

def cycles (f : Fin 9 → Fin 9) : ℕ → List (Fin 9) → List (List (Fin 9))
  | 0, _ => []
  | _+1, [] => []
  | fuel+1, a::rest =>
    let orbit := a :: ((List.range 8).map (fun j => (f^[j+1]) a)).takeWhile (fun b => b != a)
    orbit :: cycles f fuel (rest.filter (fun b => !(orbit.contains b)))

def order (f : Fin 9 → Fin 9) : List (Fin 9) :=
  match cycles f 9 (List.finRange 9) with
  | [] => []
  | a::rest => a ++ ((rest.mergeSort (fun a b => a.length ≥ b.length)).flatten)

def relabel (f : Fin 9 → Fin 9) : Equiv.Perm (Fin 9) :=
  let table := ((List.finRange 9).map f).toArray
  let cached : Fin 9 → Fin 9 := fun x => table[x.val]!
  ((List.finRange 9).zip (order cached)).foldl
    (fun r ab => r.trans (Equiv.swap ab.1 (r ab.2))) (Equiv.refl _)

def rows : List (Fin 9 → Fin 9) := [
  ![0,2,3,4,5,6,7,8,1],
  ![0,2,3,4,5,6,7,1,8],
  ![0,2,3,4,5,6,1,8,7],
  ![0,2,3,4,5,6,1,7,8],
  ![0,2,3,4,5,1,7,8,6],
  ![0,2,3,4,5,1,7,6,8],
  ![0,2,3,4,5,1,6,7,8],
  ![0,2,3,4,1,6,7,8,5],
  ![0,2,3,4,1,6,7,5,8],
  ![0,2,3,4,1,6,5,8,7],
  ![0,2,3,4,1,6,5,7,8],
  ![0,2,3,4,1,5,6,7,8],
  ![0,2,3,1,5,6,4,8,7],
  ![0,2,3,1,5,6,4,7,8],
  ![0,2,3,1,5,4,7,6,8],
  ![0,2,3,1,5,4,6,7,8],
  ![0,2,3,1,4,5,6,7,8],
  ![0,2,1,4,3,6,5,8,7],
  ![0,2,1,4,3,6,5,7,8],
  ![0,2,1,4,3,5,6,7,8],
  ![0,2,1,3,4,5,6,7,8],
  ![0,1,2,3,4,5,6,7,8],
  ![1,0,3,4,5,6,7,8,2],
  ![1,0,3,4,5,6,7,2,8],
  ![1,0,3,4,5,6,2,8,7],
  ![1,0,3,4,5,6,2,7,8],
  ![1,0,3,4,5,2,7,8,6],
  ![1,0,3,4,5,2,7,6,8],
  ![1,0,3,4,5,2,6,7,8],
  ![1,0,3,4,2,6,7,5,8],
  ![1,0,3,4,2,6,5,8,7],
  ![1,0,3,4,2,6,5,7,8],
  ![1,0,3,4,2,5,6,7,8],
  ![1,0,3,2,5,4,7,6,8],
  ![1,0,3,2,5,4,6,7,8],
  ![1,0,3,2,4,5,6,7,8],
  ![1,0,2,3,4,5,6,7,8],
  ![1,2,0,4,5,6,7,8,3],
  ![1,2,0,4,5,6,7,3,8],
  ![1,2,0,4,5,6,3,8,7],
  ![1,2,0,4,5,6,3,7,8],
  ![1,2,0,4,5,3,7,8,6],
  ![1,2,0,4,5,3,7,6,8],
  ![1,2,0,4,5,3,6,7,8],
  ![1,2,0,4,3,6,5,8,7],
  ![1,2,0,4,3,6,5,7,8],
  ![1,2,0,4,3,5,6,7,8],
  ![1,2,0,3,4,5,6,7,8],
  ![1,2,3,0,5,6,7,8,4],
  ![1,2,3,0,5,6,7,4,8],
  ![1,2,3,0,5,6,4,8,7],
  ![1,2,3,0,5,6,4,7,8],
  ![1,2,3,0,5,4,7,6,8],
  ![1,2,3,0,5,4,6,7,8],
  ![1,2,3,0,4,5,6,7,8],
  ![1,2,3,4,0,6,7,8,5],
  ![1,2,3,4,0,6,7,5,8],
  ![1,2,3,4,0,6,5,8,7],
  ![1,2,3,4,0,6,5,7,8],
  ![1,2,3,4,0,5,6,7,8],
  ![1,2,3,4,5,0,7,8,6],
  ![1,2,3,4,5,0,7,6,8],
  ![1,2,3,4,5,0,6,7,8],
  ![1,2,3,4,5,6,0,8,7],
  ![1,2,3,4,5,6,0,7,8],
  ![1,2,3,4,5,6,7,0,8],
  ![1,2,3,4,5,6,7,8,0]]

def rowTables : List (List (Fin 9)) := rows.map (fun g => (List.finRange 9).map g)

def correct (f : Equiv.Perm (Fin 9)) : Bool :=
  let r := relabel f
  let table := (List.finRange 9).map (fun x => r (f (r.symm x)))
  decide (r 0 = 0) && rowTables.contains table

@[spectrum_native]
theorem checked : (permsOfList (List.finRange 9)).all correct = true := by
  native_decide
spectrum_assert checked complete

end Spectrum.E883Nine.Canonical
