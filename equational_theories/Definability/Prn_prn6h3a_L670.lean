import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 670 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn6h3a family are assigned in when refuting equation
670. Any order is sound; this one was searched for. -/
def ordprn6h3a_Law670 : List (Fin 12) := List.finRange 12

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 670: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law670 :
    DefSearch.go 6 (Magma.toTm Law670.lhs) (Magma.toTm Law670.rhs)
      (Magma.levels prn6h3a.E prn6h3a.z prn6h3a.st prn6h3a.tr ordprn6h3a_Law670)
      (Array.replicate (6 * 6) 6) (Magma.envArrs 6 2) = true := by
  native_decide
