import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 3620 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn6h3a group on tuples: enough to prune the
search for equation 3620 exactly as hard as all `6^3` of them. -/
def envprn6h3a_Law3620 : List (Array Nat) := [#[0, 0, 0], #[0, 0, 1], #[0, 0, 2], #[0, 0, 3], #[0, 0, 4], #[0, 0, 5], #[0, 1, 0], #[0, 1, 1], #[0, 1, 2], #[0, 1, 3], #[0, 1, 4], #[0, 1, 5], #[0, 2, 0], #[0, 2, 1], #[0, 2, 2], #[0, 2, 3], #[0, 2, 4], #[0, 2, 5], #[0, 3, 0], #[0, 3, 1], #[0, 3, 2], #[0, 3, 3], #[0, 3, 4], #[0, 3, 5], #[0, 4, 0], #[0, 4, 1], #[0, 4, 2], #[0, 4, 3], #[0, 4, 4], #[0, 4, 5], #[0, 5, 0], #[0, 5, 1], #[0, 5, 2], #[0, 5, 3], #[0, 5, 4], #[0, 5, 5], #[3, 0, 0], #[3, 0, 1], #[3, 0, 2], #[3, 0, 3], #[3, 0, 4], #[3, 0, 5], #[3, 1, 0], #[3, 1, 1], #[3, 1, 2], #[3, 1, 3], #[3, 1, 4], #[3, 1, 5], #[3, 2, 0], #[3, 2, 1], #[3, 2, 2], #[3, 2, 3], #[3, 2, 4], #[3, 2, 5], #[3, 3, 0], #[3, 3, 1], #[3, 3, 2], #[3, 3, 3], #[3, 3, 4], #[3, 3, 5], #[3, 4, 0], #[3, 4, 1], #[3, 4, 2], #[3, 4, 3], #[3, 4, 4], #[3, 4, 5], #[3, 5, 0], #[3, 5, 1], #[3, 5, 2], #[3, 5, 3], #[3, 5, 4], #[3, 5, 5]]

/-- The orbits of the prn6h3a family, as the search takes them when refuting equation
3620. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn6h3a_Law3620 : List (Fin 12) := List.finRange 12

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 3620: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law3620 :
    DefSearch.go 6 (Magma.toTm Law3620.lhs) (Magma.toTm Law3620.rhs)
      ordprn6h3a_Law3620.length
      (Magma.levels prn6h3a.E prn6h3a.z prn6h3a.st prn6h3a.tr ordprn6h3a_Law3620)
      (Array.replicate (6 * 6) 6) envprn6h3a_Law3620 = true := by
  native_decide
