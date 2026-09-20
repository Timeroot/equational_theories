import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation

/-! A nine-element counterexample to transitivity of the proposed adjacency
relation on idempotents. It satisfies even E167 and E168, as well as E1483.
This refutes a proposed proof route, not a definability-table cell. -/

namespace AdjacencyCounterexample

@[implicit_reducible] def source : Magma (Fin 9) where
  op x y := (![![0, 3, 3, 0, 3, 8, 8, 8, 0],
    ![4, 1, 5, 4, 1, 1, 5, 5, 4],
    ![6, 6, 2, 7, 7, 6, 2, 2, 7],
    ![4, 1, 2, 4, 1, 1, 2, 2, 4],
    ![0, 3, 3, 0, 3, 8, 8, 8, 0],
    ![6, 6, 2, 7, 7, 6, 2, 2, 7],
    ![0, 1, 5, 0, 1, 1, 5, 5, 0],
    ![4, 3, 3, 4, 3, 8, 8, 8, 4],
    ![6, 6, 5, 7, 7, 6, 5, 5, 7]] : Fin 9 → Fin 9 → Fin 9) x y

def adjacent (x y : Fin 9) : Prop :=
  source.op (source.op x y) (source.op x y) = source.op y x ∧
  source.op (source.op y x) (source.op y x) = source.op x y

instance (x y : Fin 9) : Decidable (adjacent x y) := by
  unfold adjacent
  infer_instance

theorem counterexample :
    @Equation167 (Fin 9) source ∧ @Equation168 (Fin 9) source ∧
    @Equation1483 (Fin 9) source ∧
    source.op 0 0 = 0 ∧ source.op 1 1 = 1 ∧ source.op 2 2 = 2 ∧
    adjacent 0 1 ∧ adjacent 1 2 ∧ ¬ adjacent 0 2 := by decide

/-- info: 'AdjacencyCounterexample.counterexample' depends on axioms: [propext] -/
#guard_msgs in
#print axioms counterexample

end AdjacencyCounterexample
