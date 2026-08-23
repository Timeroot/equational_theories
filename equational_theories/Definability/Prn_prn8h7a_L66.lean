import equational_theories.Definability.Prn_prn8h7a_data
import equational_theories.Definability.Prune

/-! # No group of order 7 on Fin 8 invariant operation satisfies equation 66 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h7a family are assigned in when refuting equation
66. Any order is sound; this one was searched for. -/
def ordprn8h7a_Law66 : List (Fin 10) := [8, 1, 0, 9, 7, 3, 2, 6, 5, 4]

/-- No prn8h7a-invariant operation on `Fin 8` satisfies equation 66: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h7a_Law66 :
    DefSearch.go 8 (Magma.toTm Law66.lhs) (Magma.toTm Law66.rhs)
      (Magma.levels prn8h7a.E prn8h7a.z prn8h7a.st prn8h7a.tr ordprn8h7a_Law66)
      (Array.replicate (8 * 8) 8) (Magma.envArrs 8 2) = true := by
  native_decide
