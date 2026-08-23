import equational_theories.Definability.Lab_lab18h720a_data
import equational_theories.Definability.Prune

/-! # No labelled shuffle on Fin 18 invariant operation satisfies equation 3345 -/

set_option maxHeartbeats 4000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the lab18h720a group on tuples: enough to prune the
search for equation 3345 exactly as hard as all `18^2` of them. -/
def envtlab18h720a_Law3345 : List (List Nat) := [[0, 0], [0, 1], [0, 2], [1, 0], [1, 1], [1, 2], [2, 0], [2, 1], [2, 2], [0, 3], [0, 4], [0, 5], [1, 3], [1, 4], [1, 5], [2, 3], [2, 4], [2, 5]]

def envlab18h720a_Law3345 : List (ℕ → Fin 18) :=
  envtlab18h720a_Law3345.map fun u i ↦ ⟨u.getD i 0 % 18, Nat.mod_lt _ (by decide)⟩

/-- The order the orbits of the lab18h720a family are assigned in when refuting equation
3345. Any order is sound; this one was searched for. -/
def ordlab18h720a_Law3345 : List (Fin 18) := List.finRange 18

/-- No lab18h720a-invariant operation on `Fin 18` satisfies equation 3345: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem nolab18h720a_Law3345 : Magma.searchT lab18h720a.E Law3345
    envlab18h720a_Law3345 (ordlab18h720a_Law3345.map fun i ↦
      ((i, (List.finRange 18).filter (Magma.orbitOK lab18h720a.E lab18h720a.z lab18h720a.st i ·)),
        Magma.cells lab18h720a.tr i))
    (Array.replicate (18 * 18) none) = true := by
  native_decide
