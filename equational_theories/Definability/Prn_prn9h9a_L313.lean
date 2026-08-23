import equational_theories.Definability.Prn_prn9h9a_data
import equational_theories.Definability.Prune

/-! # No group of order 9 on Fin 9 invariant operation satisfies equation 313 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h9a family are assigned in when refuting equation
313. Any order is sound; this one was searched for. -/
def ordprn9h9a_Law313 : List (Fin 9) := [2, 7, 0, 1, 8, 6, 4, 3, 5]

/-- No prn9h9a-invariant operation on `Fin 9` satisfies equation 313: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h9a_Law313 :
    DefSearch.go 9 (Magma.toTm Law313.lhs) (Magma.toTm Law313.rhs)
      (Magma.levels prn9h9a.E prn9h9a.z prn9h9a.st prn9h9a.tr ordprn9h9a_Law313)
      (Array.replicate (9 * 9) 9) (Magma.envArrs 9 2) = true := by
  native_decide
