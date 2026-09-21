import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation

/-! A counterexample to the 42-leaf candidate found in the spectrum/priority pass.
The opposite operation satisfies the target here; this only rejects the candidate. -/

namespace SecondCandidate3342

@[implicit_reducible] def source : Magma (Fin 8) where
  op := ![![5, 1, 0, 3, 4, 7, 6, 5],
    ![1, 6, 7, 1, 4, 7, 1, 1],
    ![7, 7, 6, 2, 4, 6, 5, 0],
    ![6, 1, 5, 0, 4, 2, 0, 3],
    ![4, 4, 4, 4, 6, 4, 4, 4],
    ![0, 7, 6, 5, 4, 6, 2, 7],
    ![3, 1, 2, 0, 4, 5, 0, 6],
    ![5, 1, 7, 6, 4, 0, 3, 5]]

def candidate (x y : Fin 8) : Fin 8 :=
  let f := source.op
  let u := f y x
  let a := f (f x x) (f y y)
  let b := f (f y y) (f x x)
  let c := f (f b u) (f u b)
  let d := f a (f (f (f u b) b) a)
  f (f d c) c

@[implicit_reducible] def target : Magma (Fin 8) := ⟨candidate⟩
@[implicit_reducible] def opposite : Magma (Fin 8) := ⟨fun x y => source.op y x⟩

theorem source_law : @Equation3342 (Fin 8) source := by decide

theorem counterexample : ¬ @Equation3545 (Fin 8) target := by
  intro h
  have hbad : candidate 0 1 ≠ candidate 1 (candidate (candidate 0 0) 0) := by decide
  exact hbad (h 0 1)

theorem opposite_law : @Equation3545 (Fin 8) opposite := by decide

/-- info: 'SecondCandidate3342.counterexample' depends on axioms: [propext] -/
#guard_msgs in
#print axioms counterexample

end SecondCandidate3342
