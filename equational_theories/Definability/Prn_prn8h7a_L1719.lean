import equational_theories.Definability.Prn_prn8h7a_data
import equational_theories.Definability.Prune

/-! # No group of order 7 on Fin 8 invariant operation satisfies equation 1719 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h7a group on tuples: enough to prune the
search for equation 1719 exactly as hard as all `8^2` of them. -/
def envprn8h7a_Law1719 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[7, 0], #[7, 7]]

/-- The order the orbits of the prn8h7a family are assigned in when refuting equation
1719. Any order is sound; this one was searched for. -/
def ordprn8h7a_Law1719 : List (Fin 10) := [4, 0, 2, 9, 1, 5, 7, 6, 8, 3]

/-- No prn8h7a-invariant operation on `Fin 8` satisfies equation 1719: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h7a_Law1719 :
    DefSearch.go 8 (Magma.toTm Law1719.lhs) (Magma.toTm Law1719.rhs)
      (Magma.levels prn8h7a.E prn8h7a.z prn8h7a.st prn8h7a.tr ordprn8h7a_Law1719)
      (Array.replicate (8 * 8) 8) envprn8h7a_Law1719 = true := by
  native_decide
