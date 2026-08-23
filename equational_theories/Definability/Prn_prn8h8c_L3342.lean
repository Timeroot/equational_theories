import equational_theories.Definability.Prn_prn8h8c_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#3) invariant operation satisfies equation 3342 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8c family are assigned in when refuting equation
3342. Any order is sound; this one was searched for. -/
def ordprn8h8c_Law3342 : List (Fin 8) := [2, 0, 6, 7, 3, 1, 5, 4]

/-- No prn8h8c-invariant operation on `Fin 8` satisfies equation 3342: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8c_Law3342 :
    DefSearch.go 8 (Magma.toTm Law3342.lhs) (Magma.toTm Law3342.rhs)
      (Magma.levels prn8h8c.E prn8h8c.z prn8h8c.st prn8h8c.tr ordprn8h8c_Law3342)
      (Array.replicate (8 * 8) 8) (Magma.envArrs 8 2) = true := by
  native_decide
