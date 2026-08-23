import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 167 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn6h3a group on tuples: enough to prune the
search for equation 167 exactly as hard as all `6^2` of them. -/
def envprn6h3a_Law167 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[3, 0], #[3, 1], #[3, 2], #[3, 3], #[3, 4], #[3, 5]]

/-- The order the orbits of the prn6h3a family are assigned in when refuting equation
167. Any order is sound; this one was searched for. -/
def ordprn6h3a_Law167 : List (Fin 12) := [3, 6, 1, 0, 9, 2, 8, 10, 4, 7, 11, 5]

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 167: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law167 :
    DefSearch.go 6 (Magma.toTm Law167.lhs) (Magma.toTm Law167.rhs)
      (Magma.levels prn6h3a.E prn6h3a.z prn6h3a.st prn6h3a.tr ordprn6h3a_Law167)
      (Array.replicate (6 * 6) 6) envprn6h3a_Law167 = true := by
  native_decide
