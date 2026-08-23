import equational_theories.Definability.Prn_prn13h11a_data
import equational_theories.Definability.Prune

/-! # No group of order 11 on Fin 13 invariant operation satisfies equation 1682 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn13h11a group on tuples: enough to prune the
search for equation 1682 exactly as hard as all `13^2` of them. -/
def envprn13h11a_Law1682 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[1, 0], #[1, 1], #[1, 2], #[2, 0], #[2, 1], #[2, 2], #[2, 3], #[2, 4], #[2, 5], #[2, 6], #[2, 7], #[2, 8], #[2, 9], #[2, 10], #[2, 11], #[2, 12]]

/-- The orbits of the prn13h11a family, as the search takes them when refuting equation
1682. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn13h11a_Law1682 : List (Fin 19) := List.finRange 19

/-- No prn13h11a-invariant operation on `Fin 13` satisfies equation 1682: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn13h11a_Law1682 :
    DefSearch.go 13 (Magma.toTm Law1682.lhs) (Magma.toTm Law1682.rhs)
      ordprn13h11a_Law1682.length
      (Magma.levels prn13h11a.E prn13h11a.z prn13h11a.st prn13h11a.tr ordprn13h11a_Law1682)
      (Array.replicate (13 * 13) 13) envprn13h11a_Law1682 = true := by
  native_decide
