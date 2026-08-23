import equational_theories.Definability.Prn_prn8h4c_data
import equational_theories.Definability.Prune

/-! # No group of order 4 on Fin 8 (#3) invariant operation satisfies equation 115 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h4c group on tuples: enough to prune the
search for equation 115 exactly as hard as all `8^2` of them. -/
def envprn8h4c_Law115 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7]]

/-- The orbits of the prn8h4c family, as the search takes them when refuting equation
115. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn8h4c_Law115 : List (Fin 16) := List.finRange 16

/-- No prn8h4c-invariant operation on `Fin 8` satisfies equation 115: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h4c_Law115 :
    DefSearch.go 8 (Magma.toTm Law115.lhs) (Magma.toTm Law115.rhs)
      ordprn8h4c_Law115.length
      (Magma.levels prn8h4c.E prn8h4c.z prn8h4c.st prn8h4c.tr ordprn8h4c_Law115)
      (Array.replicate (8 * 8) 8) envprn8h4c_Law115 = true := by
  native_decide
