import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 3620 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn6h3a family are assigned in when refuting equation
3620. Any order is sound; this one was searched for. -/
def ordprn6h3a_Law3620 : List (Fin 12) := [0, 2, 1, 6, 3, 7, 9, 4, 11, 8, 10, 5]

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 3620: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law3620 : Magma.searchT prn6h3a.E Law3620
    (Magma.envs 6 3) (ordprn6h3a_Law3620.map fun i ↦
      ((i, (List.finRange 6).filter (Magma.orbitOK prn6h3a.E prn6h3a.z prn6h3a.st i ·)),
        Magma.cells prn6h3a.tr i))
    (Array.replicate (6 * 6) none) = true := by
  native_decide
