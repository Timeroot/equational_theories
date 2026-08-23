import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 1483 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn6h3a family are assigned in when refuting equation
1483. Any order is sound; this one was searched for. -/
def ordprn6h3a_Law1483 : List (Fin 12) := [1, 2, 10, 5, 3, 6, 8, 11, 9, 7, 0, 4]

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 1483: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law1483 :
    DefSearch.go 6 (Magma.toTm Law1483.lhs) (Magma.toTm Law1483.rhs)
      (Magma.levels prn6h3a.E prn6h3a.z prn6h3a.st prn6h3a.tr ordprn6h3a_Law1483)
      (Array.replicate (6 * 6) 6) (Magma.envArrs 6 3) = true := by
  native_decide
