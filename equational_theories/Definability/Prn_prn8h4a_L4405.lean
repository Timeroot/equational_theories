import equational_theories.Definability.Prn_prn8h4a_data
import equational_theories.Definability.Prune

/-! # No group of order 4 on Fin 8 invariant operation satisfies equation 4405 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h4a group on tuples: enough to prune the
search for equation 4405 exactly as hard as all `8^2` of them. -/
def envprn8h4a_Law4405 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[2, 0], #[2, 1], #[2, 2], #[2, 3], #[2, 4], #[2, 5], #[2, 6], #[2, 7]]

/-- The orbits of the prn8h4a family, as the search takes them when refuting equation
4405. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn8h4a_Law4405 : List (Fin 16) := List.finRange 16

/-- No prn8h4a-invariant operation on `Fin 8` satisfies equation 4405: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h4a_Law4405 :
    DefSearch.go 8 (Magma.toTm Law4405.lhs) (Magma.toTm Law4405.rhs)
      ordprn8h4a_Law4405.length
      (Magma.levels prn8h4a.E prn8h4a.z prn8h4a.st prn8h4a.tr ordprn8h4a_Law4405)
      (Array.replicate (8 * 8) 8) envprn8h4a_Law4405 = true := by
  native_decide
