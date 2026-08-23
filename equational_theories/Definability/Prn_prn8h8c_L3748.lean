import equational_theories.Definability.Prn_prn8h8c_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#3) invariant operation satisfies equation 3748 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h8c group on tuples: enough to prune the
search for equation 3748 exactly as hard as all `8^2` of them. -/
def envprn8h8c_Law3748 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7]]

/-- The orbits of the prn8h8c family, as the search takes them when refuting equation
3748. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn8h8c_Law3748 : List (Fin 8) := List.finRange 8

/-- No prn8h8c-invariant operation on `Fin 8` satisfies equation 3748: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8c_Law3748 :
    DefSearch.go 8 (Magma.toTm Law3748.lhs) (Magma.toTm Law3748.rhs)
      ordprn8h8c_Law3748.length
      (Magma.levels prn8h8c.E prn8h8c.z prn8h8c.st prn8h8c.tr ordprn8h8c_Law3748)
      (Array.replicate (8 * 8) 8) envprn8h8c_Law3748 = true := by
  native_decide
