import equational_theories.Definability.Prn_prn7h5a_data
import equational_theories.Definability.Prune

/-! # No group of order 5 on Fin 7 invariant operation satisfies equation 870 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn7h5a group on tuples: enough to prune the
search for equation 870 exactly as hard as all `7^2` of them. -/
def envprn7h5a_Law870 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[1, 0], #[1, 1], #[1, 5], #[5, 0], #[5, 1], #[5, 5]]

/-- The order the orbits of the prn7h5a family are assigned in when refuting equation
870. Any order is sound; this one was searched for. -/
def ordprn7h5a_Law870 : List (Fin 13) := [4, 12, 0, 6, 11, 8, 1, 9, 5, 7, 2, 10, 3]

/-- No prn7h5a-invariant operation on `Fin 7` satisfies equation 870: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h5a_Law870 :
    DefSearch.go 7 (Magma.toTm Law870.lhs) (Magma.toTm Law870.rhs)
      (Magma.levels prn7h5a.E prn7h5a.z prn7h5a.st prn7h5a.tr ordprn7h5a_Law870)
      (Array.replicate (7 * 7) 7) envprn7h5a_Law870 = true := by
  native_decide
