import equational_theories.Definability.Prn_prn7h5a_data
import equational_theories.Definability.Prune

/-! # No group of order 5 on Fin 7 invariant operation satisfies equation 667 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn7h5a family are assigned in when refuting equation
667. Any order is sound; this one was searched for. -/
def ordprn7h5a_Law667 : List (Fin 13) := [1, 9, 2, 10, 11, 12, 0, 8, 5, 7, 6, 3, 4]

/-- No prn7h5a-invariant operation on `Fin 7` satisfies equation 667: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h5a_Law667 :
    DefSearch.go 7 (Magma.toTm Law667.lhs) (Magma.toTm Law667.rhs)
      (Magma.levels prn7h5a.E prn7h5a.z prn7h5a.st prn7h5a.tr ordprn7h5a_Law667)
      (Array.replicate (7 * 7) 7) (Magma.envArrs 7 2) = true := by
  native_decide
