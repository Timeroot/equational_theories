import equational_theories.Definability.Prn_prn7h5a_data
import equational_theories.Definability.Prune

/-! # No group of order 5 on Fin 7 invariant operation satisfies equation 978 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn7h5a family are assigned in when refuting equation
978. Any order is sound; this one was searched for. -/
def ordprn7h5a_Law978 : List (Fin 13) := [12, 2, 9, 5, 8, 0, 7, 11, 6, 1, 10, 4, 3]

/-- No prn7h5a-invariant operation on `Fin 7` satisfies equation 978: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h5a_Law978 :
    DefSearch.go 7 (Magma.toTm Law978.lhs) (Magma.toTm Law978.rhs)
      (Magma.levels prn7h5a.E prn7h5a.z prn7h5a.st prn7h5a.tr ordprn7h5a_Law978)
      (Array.replicate (7 * 7) 7) (Magma.envArrs 7 3) = true := by
  native_decide
