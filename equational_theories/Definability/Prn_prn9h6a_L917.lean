import equational_theories.Definability.Prn_prn9h6a_data
import equational_theories.Definability.Prune

/-! # No group of order 6 on Fin 9 invariant operation satisfies equation 917 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h6a family are assigned in when refuting equation
917. Any order is sound; this one was searched for. -/
def ordprn9h6a_Law917 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No prn9h6a-invariant operation on `Fin 9` satisfies equation 917: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h6a_Law917 :
    DefSearch.go 9 (Magma.toTm Law917.lhs) (Magma.toTm Law917.rhs)
      (Magma.levels prn9h6a.E prn9h6a.z prn9h6a.st prn9h6a.tr ordprn9h6a_Law917)
      (Array.replicate (9 * 9) 9) (Magma.envArrs 9 2) = true := by
  native_decide
