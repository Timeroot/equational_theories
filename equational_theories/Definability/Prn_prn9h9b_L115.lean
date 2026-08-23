import equational_theories.Definability.Prn_prn9h9b_data
import equational_theories.Definability.Prune

/-! # No group of order 9 on Fin 9 (#2) invariant operation satisfies equation 115 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h9b family are assigned in when refuting equation
115. Any order is sound; this one was searched for. -/
def ordprn9h9b_Law115 : List (Fin 9) := [0, 2, 3, 1, 6, 5, 7, 4, 8]

/-- No prn9h9b-invariant operation on `Fin 9` satisfies equation 115: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h9b_Law115 :
    DefSearch.go 9 (Magma.toTm Law115.lhs) (Magma.toTm Law115.rhs)
      (Magma.levels prn9h9b.E prn9h9b.z prn9h9b.st prn9h9b.tr ordprn9h9b_Law115)
      (Array.replicate (9 * 9) 9) (Magma.envArrs 9 2) = true := by
  native_decide
