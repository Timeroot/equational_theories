import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 3675 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn6h3a group on tuples: enough to prune the
search for equation 3675 exactly as hard as all `6^2` of them. -/
def envprn6h3a_Law3675 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[3, 0], #[3, 1], #[3, 2], #[3, 3], #[3, 4], #[3, 5]]

/-- The order the orbits of the prn6h3a family are assigned in when refuting equation
3675. Any order is sound; this one was searched for. -/
def ordprn6h3a_Law3675 : List (Fin 12) := [0, 11, 4, 9, 2, 1, 5, 10, 6, 7, 3, 8]

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 3675: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law3675 :
    DefSearch.go 6 (Magma.toTm Law3675.lhs) (Magma.toTm Law3675.rhs)
      (Magma.levels prn6h3a.E prn6h3a.z prn6h3a.st prn6h3a.tr ordprn6h3a_Law3675)
      (Array.replicate (6 * 6) 6) envprn6h3a_Law3675 = true := by
  native_decide
