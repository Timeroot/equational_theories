import equational_theories.Definability.Prn_prn6h2a_data
import equational_theories.Definability.Prune

/-! # No group of order 2 on Fin 6 invariant operation satisfies equation 504 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn6h2a group on tuples: enough to prune the
search for equation 504 exactly as hard as all `6^2` of them. -/
def envprn6h2a_Law504 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[2, 0], #[2, 1], #[2, 2], #[2, 3], #[2, 4], #[2, 5], #[4, 0], #[4, 1], #[4, 2], #[4, 3], #[4, 4], #[4, 5]]

/-- The order the orbits of the prn6h2a family are assigned in when refuting equation
504. Any order is sound; this one was searched for. -/
def ordprn6h2a_Law504 : List (Fin 18) := List.finRange 18

/-- No prn6h2a-invariant operation on `Fin 6` satisfies equation 504: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h2a_Law504 :
    DefSearch.go 6 (Magma.toTm Law504.lhs) (Magma.toTm Law504.rhs)
      (Magma.levels prn6h2a.E prn6h2a.z prn6h2a.st prn6h2a.tr ordprn6h2a_Law504)
      (Array.replicate (6 * 6) 6) envprn6h2a_Law504 = true := by
  native_decide
