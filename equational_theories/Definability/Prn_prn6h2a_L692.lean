import equational_theories.Definability.Prn_prn6h2a_data
import equational_theories.Definability.Prune

/-! # No group of order 2 on Fin 6 invariant operation satisfies equation 692 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn6h2a group on tuples: enough to prune the
search for equation 692 exactly as hard as all `6^3` of them. -/
def envprn6h2a_Law692 : List (Array Nat) := [#[0, 0, 0], #[0, 0, 1], #[0, 0, 2], #[0, 0, 3], #[0, 0, 4], #[0, 0, 5], #[0, 1, 0], #[0, 1, 1], #[0, 1, 2], #[0, 1, 3], #[0, 1, 4], #[0, 1, 5], #[0, 2, 0], #[0, 2, 1], #[0, 2, 2], #[0, 2, 3], #[0, 2, 4], #[0, 2, 5], #[0, 3, 0], #[0, 3, 1], #[0, 3, 2], #[0, 3, 3], #[0, 3, 4], #[0, 3, 5], #[0, 4, 0], #[0, 4, 1], #[0, 4, 2], #[0, 4, 3], #[0, 4, 4], #[0, 4, 5], #[0, 5, 0], #[0, 5, 1], #[0, 5, 2], #[0, 5, 3], #[0, 5, 4], #[0, 5, 5], #[2, 0, 0], #[2, 0, 1], #[2, 0, 2], #[2, 0, 3], #[2, 0, 4], #[2, 0, 5], #[2, 1, 0], #[2, 1, 1], #[2, 1, 2], #[2, 1, 3], #[2, 1, 4], #[2, 1, 5], #[2, 2, 0], #[2, 2, 1], #[2, 2, 2], #[2, 2, 3], #[2, 2, 4], #[2, 2, 5], #[2, 3, 0], #[2, 3, 1], #[2, 3, 2], #[2, 3, 3], #[2, 3, 4], #[2, 3, 5], #[2, 4, 0], #[2, 4, 1], #[2, 4, 2], #[2, 4, 3], #[2, 4, 4], #[2, 4, 5], #[2, 5, 0], #[2, 5, 1], #[2, 5, 2], #[2, 5, 3], #[2, 5, 4], #[2, 5, 5], #[4, 0, 0], #[4, 0, 1], #[4, 0, 2], #[4, 0, 3], #[4, 0, 4], #[4, 0, 5], #[4, 1, 0], #[4, 1, 1], #[4, 1, 2], #[4, 1, 3], #[4, 1, 4], #[4, 1, 5], #[4, 2, 0], #[4, 2, 1], #[4, 2, 2], #[4, 2, 3], #[4, 2, 4], #[4, 2, 5], #[4, 3, 0], #[4, 3, 1], #[4, 3, 2], #[4, 3, 3], #[4, 3, 4], #[4, 3, 5], #[4, 4, 0], #[4, 4, 1], #[4, 4, 2], #[4, 4, 3], #[4, 4, 4], #[4, 4, 5], #[4, 5, 0], #[4, 5, 1], #[4, 5, 2], #[4, 5, 3], #[4, 5, 4], #[4, 5, 5]]

/-- The orbits of the prn6h2a family, as the search takes them when refuting equation
692. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn6h2a_Law692 : List (Fin 18) := List.finRange 18

/-- No prn6h2a-invariant operation on `Fin 6` satisfies equation 692: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h2a_Law692 :
    DefSearch.go 6 (Magma.toTm Law692.lhs) (Magma.toTm Law692.rhs)
      ordprn6h2a_Law692.length
      (Magma.levels prn6h2a.E prn6h2a.z prn6h2a.st prn6h2a.tr ordprn6h2a_Law692)
      (Array.replicate (6 * 6) 6) envprn6h2a_Law692 = true := by
  native_decide
