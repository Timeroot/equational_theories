import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation

/-! A counterexample to the 22-leaf candidate that passed the older bank.
The opposite operation works on this model, so this is not a row refutation. -/

namespace ResidualCandidate3342

@[implicit_reducible] def source : Magma (Fin 8) where
  op x y := (![![1, 4, 0, 3, 1, 1, 6, 0],
    ![0, 3, 2, 7, 4, 4, 1, 3],
    ![0, 2, 1, 0, 0, 0, 0, 2],
    ![6, 1, 0, 0, 3, 3, 0, 7],
    ![1, 0, 0, 6, 1, 1, 3, 4],
    ![1, 0, 0, 6, 1, 1, 3, 4],
    ![3, 7, 0, 0, 6, 6, 0, 1],
    ![4, 3, 2, 1, 0, 0, 7, 3]] : Fin 8 → Fin 8 → Fin 8) x y

def candidate (x y : Fin 8) : Fin 8 :=
  let f := source.op
  let u := f y x
  let a := f (f y y) (f x x)
  let b := f (f x x) (f y y)
  f (f (f (f (f u a) a) b) b) (f u u)

@[implicit_reducible] def target : Magma (Fin 8) where
  op := candidate

@[implicit_reducible] def opposite : Magma (Fin 8) where
  op x y := source.op y x

theorem source_law : @Equation3342 (Fin 8) source := by decide

theorem counterexample : ¬ @Equation3545 (Fin 8) target := by
  intro h
  have hbad : candidate 2 3 ≠ candidate 3 (candidate (candidate 2 2) 2) := by decide
  exact hbad (h 2 3)

theorem opposite_law : @Equation3545 (Fin 8) opposite := by decide

/-- info: 'ResidualCandidate3342.counterexample' depends on axioms: [propext] -/
#guard_msgs in
#print axioms counterexample

end ResidualCandidate3342
