import equational_theories.Definability.Prn_prn8h8c_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#3) invariant operation satisfies equation 3545 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h8c group on tuples: enough to prune the
search for equation 3545 exactly as hard as all `8^2` of them. -/
def envprn8h8c_Law3545 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7]]

/-- The order the orbits of the prn8h8c family are assigned in when refuting equation
3545. Any order is sound; this one was searched for. -/
def ordprn8h8c_Law3545 : List (Fin 8) := [0, 7, 4, 2, 3, 5, 1, 6]

/-- No prn8h8c-invariant operation on `Fin 8` satisfies equation 3545: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8c_Law3545 :
    DefSearch.go 8 (Magma.toTm Law3545.lhs) (Magma.toTm Law3545.rhs)
      (Magma.levels prn8h8c.E prn8h8c.z prn8h8c.st prn8h8c.tr ordprn8h8c_Law3545)
      (Array.replicate (8 * 8) 8) envprn8h8c_Law3545 = true := by
  native_decide
