import equational_theories.Definability.Prn_prn15h3456a_data
import equational_theories.Definability.Prune

/-! # No group of order 3456 on Fin 15 invariant operation satisfies equation 1479 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn15h3456a group on tuples: enough to prune the
search for equation 1479 exactly as hard as all `15^2` of them. -/
def envprn15h3456a_Law1479 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 7], #[0, 11], #[0, 12], #[7, 0], #[7, 1], #[7, 2], #[7, 7], #[7, 11], #[7, 12]]

/-- The orbits of the prn15h3456a family, as the search takes them when refuting equation
1479. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn15h3456a_Law1479 : List (Fin 13) := List.finRange 13

/-- No prn15h3456a-invariant operation on `Fin 15` satisfies equation 1479: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn15h3456a_Law1479 :
    DefSearch.go 15 (Magma.toTm Law1479.lhs) (Magma.toTm Law1479.rhs)
      ordprn15h3456a_Law1479.length
      (Magma.levels prn15h3456a.E prn15h3456a.z prn15h3456a.st prn15h3456a.tr ordprn15h3456a_Law1479)
      (Array.replicate (15 * 15) 15) envprn15h3456a_Law1479 = true := by
  native_decide
