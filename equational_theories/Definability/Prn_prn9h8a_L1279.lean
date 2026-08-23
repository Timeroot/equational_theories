import equational_theories.Definability.Prn_prn9h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 invariant operation satisfies equation 1279 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h8a group on tuples: enough to prune the
search for equation 1279 exactly as hard as all `9^2` of them. -/
def envprn9h8a_Law1279 : List (Array Nat) := [#[0, 0], #[0, 1], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7], #[1, 8]]

/-- The orbits of the prn9h8a family, as the search takes them when refuting equation
1279. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn9h8a_Law1279 : List (Fin 11) := List.finRange 11

/-- No prn9h8a-invariant operation on `Fin 9` satisfies equation 1279: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8a_Law1279 :
    DefSearch.go 9 (Magma.toTm Law1279.lhs) (Magma.toTm Law1279.rhs)
      ordprn9h8a_Law1279.length
      (Magma.levels prn9h8a.E prn9h8a.z prn9h8a.st prn9h8a.tr ordprn9h8a_Law1279)
      (Array.replicate (9 * 9) 9) envprn9h8a_Law1279 = true := by
  native_decide
