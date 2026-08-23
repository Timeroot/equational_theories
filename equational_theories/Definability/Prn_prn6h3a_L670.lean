import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 670 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn6h3a group on tuples: enough to prune the
search for equation 670 exactly as hard as all `6^2` of them. -/
def envprn6h3a_Law670 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[3, 0], #[3, 1], #[3, 2], #[3, 3], #[3, 4], #[3, 5]]

/-- The orbits of the prn6h3a family, as the search takes them when refuting equation
670. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn6h3a_Law670 : List (Fin 12) := List.finRange 12

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 670: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law670 :
    DefSearch.go 6 (Magma.toTm Law670.lhs) (Magma.toTm Law670.rhs)
      ordprn6h3a_Law670.length
      (Magma.levels prn6h3a.E prn6h3a.z prn6h3a.st prn6h3a.tr ordprn6h3a_Law670)
      (Array.replicate (6 * 6) 6) envprn6h3a_Law670 = true := by
  native_decide
