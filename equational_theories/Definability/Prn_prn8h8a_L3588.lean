import equational_theories.Definability.Prn_prn8h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 invariant operation satisfies equation 3588 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8a family are assigned in when refuting equation
3588. Any order is sound; this one was searched for. -/
def ordprn8h8a_Law3588 : List (Fin 12) := [6, 3, 0, 2, 7, 5, 9, 11, 1, 8, 4, 10]

/-- No prn8h8a-invariant operation on `Fin 8` satisfies equation 3588: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8a_Law3588 :
    DefSearch.go 8 (Magma.toTm Law3588.lhs) (Magma.toTm Law3588.rhs)
      (Magma.levels prn8h8a.E prn8h8a.z prn8h8a.st prn8h8a.tr ordprn8h8a_Law3588)
      (Array.replicate (8 * 8) 8) (Magma.envArrs 8 3) = true := by
  native_decide
