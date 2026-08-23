import equational_theories.Definability.Prn_prn8h4b_data
import equational_theories.Definability.Prune

/-! # No group of order 4 on Fin 8 (#2) invariant operation satisfies equation 313 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h4b family are assigned in when refuting equation
313. Any order is sound; this one was searched for. -/
def ordprn8h4b_Law313 : List (Fin 16) := List.finRange 16

/-- No prn8h4b-invariant operation on `Fin 8` satisfies equation 313: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h4b_Law313 :
    DefSearch.go 8 (Magma.toTm Law313.lhs) (Magma.toTm Law313.rhs)
      (Magma.levels prn8h4b.E prn8h4b.z prn8h4b.st prn8h4b.tr ordprn8h4b_Law313)
      (Array.replicate (8 * 8) 8) (Magma.envArrs 8 2) = true := by
  native_decide
