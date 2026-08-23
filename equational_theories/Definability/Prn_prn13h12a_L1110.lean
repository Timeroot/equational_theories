import equational_theories.Definability.Prn_prn13h12a_data
import equational_theories.Definability.Prune

/-! # No group of order 12 on Fin 13 invariant operation satisfies equation 1110 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn13h12a group on tuples: enough to prune the
search for equation 1110 exactly as hard as all `13^2` of them. -/
def envprn13h12a_Law1110 : List (Array Nat) := [#[0, 0], #[0, 1], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7], #[1, 8], #[1, 9], #[1, 10], #[1, 11], #[1, 12]]

/-- The orbits of the prn13h12a family, as the search takes them when refuting equation
1110. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn13h12a_Law1110 : List (Fin 15) := List.finRange 15

/-- No prn13h12a-invariant operation on `Fin 13` satisfies equation 1110: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn13h12a_Law1110 :
    DefSearch.go 13 (Magma.toTm Law1110.lhs) (Magma.toTm Law1110.rhs)
      ordprn13h12a_Law1110.length
      (Magma.levels prn13h12a.E prn13h12a.z prn13h12a.st prn13h12a.tr ordprn13h12a_Law1110)
      (Array.replicate (13 * 13) 13) envprn13h12a_Law1110 = true := by
  native_decide
