import equational_theories.Definability.Prn_prn8h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 invariant operation satisfies equation 3352 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8a family are assigned in when refuting equation
3352. Any order is sound; this one was searched for. -/
def ordprn8h8a_Law3352 : List (Fin 12) := [6, 0, 3, 8, 11, 9, 10, 5, 4, 7, 2, 1]

/-- No prn8h8a-invariant operation on `Fin 8` satisfies equation 3352: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8a_Law3352 :
    DefSearch.go 8 (Magma.toTm Law3352.lhs) (Magma.toTm Law3352.rhs)
      (Magma.levels prn8h8a.E prn8h8a.z prn8h8a.st prn8h8a.tr ordprn8h8a_Law3352)
      (Array.replicate (8 * 8) 8) (Magma.envArrs 8 2) = true := by
  native_decide
