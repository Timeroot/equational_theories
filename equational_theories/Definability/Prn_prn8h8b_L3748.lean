import equational_theories.Definability.Prn_prn8h8b_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#2) invariant operation satisfies equation 3748 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8b family are assigned in when refuting equation
3748. Any order is sound; this one was searched for. -/
def ordprn8h8b_Law3748 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No prn8h8b-invariant operation on `Fin 8` satisfies equation 3748: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8b_Law3748 :
    DefSearch.go 8 (Magma.toTm Law3748.lhs) (Magma.toTm Law3748.rhs)
      (Magma.levels prn8h8b.E prn8h8b.z prn8h8b.st prn8h8b.tr ordprn8h8b_Law3748)
      (Array.replicate (8 * 8) 8) (Magma.envArrs 8 2) = true := by
  native_decide
