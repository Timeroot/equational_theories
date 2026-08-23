import equational_theories.Definability.Prn_prn6h2a_data
import equational_theories.Definability.Prune

/-! # No group of order 2 on Fin 6 invariant operation satisfies equation 1719 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn6h2a family are assigned in when refuting equation
1719. Any order is sound; this one was searched for. -/
def ordprn6h2a_Law1719 : List (Fin 18) := [6, 3, 8, 17, 0, 16, 7, 10, 2, 1, 4, 11, 9, 5, 14, 15, 13, 12]

/-- No prn6h2a-invariant operation on `Fin 6` satisfies equation 1719: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h2a_Law1719 :
    DefSearch.go 6 (Magma.toTm Law1719.lhs) (Magma.toTm Law1719.rhs)
      (Magma.levels prn6h2a.E prn6h2a.z prn6h2a.st prn6h2a.tr ordprn6h2a_Law1719)
      (Array.replicate (6 * 6) 6) (Magma.envArrs 6 2) = true := by
  native_decide
