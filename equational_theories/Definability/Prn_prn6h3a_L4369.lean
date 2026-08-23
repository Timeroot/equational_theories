import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 4369 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn6h3a group on tuples: enough to prune the
search for equation 4369 exactly as hard as all `6^3` of them. -/
def envprn6h3a_Law4369 : List (Array Nat) := [#[0, 0, 0], #[0, 0, 1], #[0, 0, 2], #[0, 0, 3], #[0, 0, 4], #[0, 0, 5], #[0, 1, 0], #[0, 1, 1], #[0, 1, 2], #[0, 1, 3], #[0, 1, 4], #[0, 1, 5], #[0, 2, 0], #[0, 2, 1], #[0, 2, 2], #[0, 2, 3], #[0, 2, 4], #[0, 2, 5], #[0, 3, 0], #[0, 3, 1], #[0, 3, 2], #[0, 3, 3], #[0, 3, 4], #[0, 3, 5], #[0, 4, 0], #[0, 4, 1], #[0, 4, 2], #[0, 4, 3], #[0, 4, 4], #[0, 4, 5], #[0, 5, 0], #[0, 5, 1], #[0, 5, 2], #[0, 5, 3], #[0, 5, 4], #[0, 5, 5], #[3, 0, 0], #[3, 0, 1], #[3, 0, 2], #[3, 0, 3], #[3, 0, 4], #[3, 0, 5], #[3, 1, 0], #[3, 1, 1], #[3, 1, 2], #[3, 1, 3], #[3, 1, 4], #[3, 1, 5], #[3, 2, 0], #[3, 2, 1], #[3, 2, 2], #[3, 2, 3], #[3, 2, 4], #[3, 2, 5], #[3, 3, 0], #[3, 3, 1], #[3, 3, 2], #[3, 3, 3], #[3, 3, 4], #[3, 3, 5], #[3, 4, 0], #[3, 4, 1], #[3, 4, 2], #[3, 4, 3], #[3, 4, 4], #[3, 4, 5], #[3, 5, 0], #[3, 5, 1], #[3, 5, 2], #[3, 5, 3], #[3, 5, 4], #[3, 5, 5]]

/-- The order the orbits of the prn6h3a family are assigned in when refuting equation
4369. Any order is sound; this one was searched for. -/
def ordprn6h3a_Law4369 : List (Fin 12) := List.finRange 12

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 4369: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law4369 :
    DefSearch.go 6 (Magma.toTm Law4369.lhs) (Magma.toTm Law4369.rhs)
      (Magma.levels prn6h3a.E prn6h3a.z prn6h3a.st prn6h3a.tr ordprn6h3a_Law4369)
      (Array.replicate (6 * 6) 6) envprn6h3a_Law4369 = true := by
  native_decide
