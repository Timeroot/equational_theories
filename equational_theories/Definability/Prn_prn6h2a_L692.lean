import equational_theories.Definability.Prn_prn6h2a_data
import equational_theories.Definability.Prune

/-! # No group of order 2 on Fin 6 invariant operation satisfies equation 692 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn6h2a family are assigned in when refuting equation
692. Any order is sound; this one was searched for. -/
def ordprn6h2a_Law692 : List (Fin 18) := [3, 17, 12, 1, 4, 16, 10, 13, 11, 15, 9, 2, 8, 6, 7, 0, 14, 5]

/-- No prn6h2a-invariant operation on `Fin 6` satisfies equation 692: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h2a_Law692 :
    DefSearch.go 6 (Magma.toTm Law692.lhs) (Magma.toTm Law692.rhs)
      (Magma.levels prn6h2a.E prn6h2a.z prn6h2a.st prn6h2a.tr ordprn6h2a_Law692)
      (Array.replicate (6 * 6) 6) (Magma.envArrs 6 3) = true := by
  native_decide
