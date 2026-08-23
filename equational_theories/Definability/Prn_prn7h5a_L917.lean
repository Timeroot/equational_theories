import equational_theories.Definability.Prn_prn7h5a_data
import equational_theories.Definability.Prune

/-! # No group of order 5 on Fin 7 invariant operation satisfies equation 917 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn7h5a group on tuples: enough to prune the
search for equation 917 exactly as hard as all `7^2` of them. -/
def envprn7h5a_Law917 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[1, 0], #[1, 1], #[1, 5], #[5, 0], #[5, 1], #[5, 5]]

/-- The order the orbits of the prn7h5a family are assigned in when refuting equation
917. Any order is sound; this one was searched for. -/
def ordprn7h5a_Law917 : List (Fin 13) := [0, 8, 9, 10, 11, 12, 4, 3, 5, 2, 7, 6, 1]

/-- No prn7h5a-invariant operation on `Fin 7` satisfies equation 917: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h5a_Law917 :
    DefSearch.go 7 (Magma.toTm Law917.lhs) (Magma.toTm Law917.rhs)
      (Magma.levels prn7h5a.E prn7h5a.z prn7h5a.st prn7h5a.tr ordprn7h5a_Law917)
      (Array.replicate (7 * 7) 7) envprn7h5a_Law917 = true := by
  native_decide
