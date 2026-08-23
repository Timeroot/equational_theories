import equational_theories.Definability.Prn_prn8h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 invariant operation satisfies equation 707 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h8a group on tuples: enough to prune the
search for equation 707 exactly as hard as all `8^2` of them. -/
def envprn8h8a_Law707 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 4], #[0, 5], #[0, 6], #[4, 0], #[4, 1], #[4, 2], #[4, 4], #[4, 5], #[4, 6]]

/-- The order the orbits of the prn8h8a family are assigned in when refuting equation
707. Any order is sound; this one was searched for. -/
def ordprn8h8a_Law707 : List (Fin 12) := [8, 5, 11, 10, 0, 9, 6, 3, 7, 2, 1, 4]

/-- No prn8h8a-invariant operation on `Fin 8` satisfies equation 707: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8a_Law707 :
    DefSearch.go 8 (Magma.toTm Law707.lhs) (Magma.toTm Law707.rhs)
      (Magma.levels prn8h8a.E prn8h8a.z prn8h8a.st prn8h8a.tr ordprn8h8a_Law707)
      (Array.replicate (8 * 8) 8) envprn8h8a_Law707 = true := by
  native_decide
