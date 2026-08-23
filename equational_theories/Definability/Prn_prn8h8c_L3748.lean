import equational_theories.Definability.Prn_prn8h8c_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#3) invariant operation satisfies equation 3748 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8c family are assigned in when refuting equation
3748. Any order is sound; this one was searched for. -/
def ordprn8h8c_Law3748 : List (Fin 8) := [0, 3, 1, 6, 5, 7, 2, 4]

/-- No prn8h8c-invariant operation on `Fin 8` satisfies equation 3748: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8c_Law3748 :
    DefSearch.go 8 (Magma.toTm Law3748.lhs) (Magma.toTm Law3748.rhs)
      (Magma.levels prn8h8c.E prn8h8c.z prn8h8c.st prn8h8c.tr ordprn8h8c_Law3748)
      (Array.replicate (8 * 8) 8) (Magma.envArrs 8 2) = true := by
  native_decide
