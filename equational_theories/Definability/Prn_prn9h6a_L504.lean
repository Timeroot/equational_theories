import equational_theories.Definability.Prn_prn9h6a_data
import equational_theories.Definability.Prune

/-! # No group of order 6 on Fin 9 invariant operation satisfies equation 504 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h6a group on tuples: enough to prune the
search for equation 504 exactly as hard as all `9^2` of them. -/
def envprn9h6a_Law504 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 5], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7], #[1, 8]]

/-- The orbits of the prn9h6a family, as the search takes them when refuting equation
504. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn9h6a_Law504 : List (Fin 14) := List.finRange 14

/-- No prn9h6a-invariant operation on `Fin 9` satisfies equation 504: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h6a_Law504 :
    DefSearch.go 9 (Magma.toTm Law504.lhs) (Magma.toTm Law504.rhs)
      ordprn9h6a_Law504.length
      (Magma.levels prn9h6a.E prn9h6a.z prn9h6a.st prn9h6a.tr ordprn9h6a_Law504)
      (Array.replicate (9 * 9) 9) envprn9h6a_Law504 = true := by
  native_decide
