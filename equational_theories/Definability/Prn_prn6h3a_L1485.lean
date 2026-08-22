import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 1485 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn6h3a family are assigned in when refuting equation
1485. Any order is sound; this one was searched for. -/
def ordprn6h3a_Law1485 : List (Fin 12) := [8, 0, 3, 11, 2, 9, 4, 6, 5, 7, 1, 10]

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 1485: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law1485 : Magma.searchT prn6h3a.E Law1485
    (Magma.envs 6 3) (ordprn6h3a_Law1485.map fun i ↦
      ((i, (List.finRange 6).filter (Magma.orbitOK prn6h3a.E prn6h3a.z prn6h3a.st i ·)),
        Magma.cells prn6h3a.tr i))
    (Array.replicate (6 * 6) none) = true := by
  native_decide
