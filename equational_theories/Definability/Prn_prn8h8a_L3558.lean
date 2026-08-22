import equational_theories.Definability.Prn_prn8h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 invariant operation satisfies equation 3558 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8a family are assigned in when refuting equation
3558. Any order is sound; this one was searched for. -/
def ordprn8h8a_Law3558 : List (Fin 12) := [2, 0, 9, 3, 8, 6, 11, 5, 7, 1, 4, 10]

/-- No prn8h8a-invariant operation on `Fin 8` satisfies equation 3558: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8a_Law3558 : Magma.searchT prn8h8a.E Law3558
    (Magma.envs 8 2) (ordprn8h8a_Law3558.map fun i ↦
      ((i, (List.finRange 8).filter (Magma.orbitOK prn8h8a.E prn8h8a.z prn8h8a.st i ·)),
        Magma.cells prn8h8a.tr i))
    (Array.replicate (8 * 8) none) = true := by
  native_decide
