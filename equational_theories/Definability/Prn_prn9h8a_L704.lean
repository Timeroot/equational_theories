import equational_theories.Definability.Prn_prn9h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 invariant operation satisfies equation 704 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h8a family are assigned in when refuting equation
704. Any order is sound; this one was searched for. -/
def ordprn9h8a_Law704 : List (Fin 11) := List.finRange 11

/-- No prn9h8a-invariant operation on `Fin 9` satisfies equation 704: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8a_Law704 :
    DefSearch.go 9 (Magma.toTm Law704.lhs) (Magma.toTm Law704.rhs)
      (Magma.levels prn9h8a.E prn9h8a.z prn9h8a.st prn9h8a.tr ordprn9h8a_Law704)
      (Array.replicate (9 * 9) 9) (Magma.envArrs 9 2) = true := by
  native_decide
