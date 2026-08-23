import equational_theories.Definability.Prn_prn8h8d_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#4) invariant operation satisfies equation 3548 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h8d group on tuples: enough to prune the
search for equation 3548 exactly as hard as all `8^2` of them. -/
def envprn8h8d_Law3548 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7]]

/-- The order the orbits of the prn8h8d family are assigned in when refuting equation
3548. Any order is sound; this one was searched for. -/
def ordprn8h8d_Law3548 : List (Fin 8) := [2, 4, 5, 1, 6, 3, 7, 0]

/-- No prn8h8d-invariant operation on `Fin 8` satisfies equation 3548: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8d_Law3548 :
    DefSearch.go 8 (Magma.toTm Law3548.lhs) (Magma.toTm Law3548.rhs)
      (Magma.levels prn8h8d.E prn8h8d.z prn8h8d.st prn8h8d.tr ordprn8h8d_Law3548)
      (Array.replicate (8 * 8) 8) envprn8h8d_Law3548 = true := by
  native_decide
