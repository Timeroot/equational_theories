import equational_theories.Definability.Prn_prn9h6a_data
import equational_theories.Definability.Prune

/-! # No group of order 6 on Fin 9 invariant operation satisfies equation 870 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h6a family are assigned in when refuting equation
870. Any order is sound; this one was searched for. -/
def ordprn9h6a_Law870 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No prn9h6a-invariant operation on `Fin 9` satisfies equation 870: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h6a_Law870 :
    DefSearch.go 9 (Magma.toTm Law870.lhs) (Magma.toTm Law870.rhs)
      (Magma.levels prn9h6a.E prn9h6a.z prn9h6a.st prn9h6a.tr ordprn9h6a_Law870)
      (Array.replicate (9 * 9) 9) (Magma.envArrs 9 2) = true := by
  native_decide
