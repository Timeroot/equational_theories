import equational_theories.Definability.Prn_prn8h8d_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#4) invariant operation satisfies equation 3548 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8d family are assigned in when refuting equation
3548. Any order is sound; this one was searched for. -/
def ordprn8h8d_Law3548 : List (Fin 8) := [2, 4, 5, 1, 6, 3, 7, 0]

/-- No prn8h8d-invariant operation on `Fin 8` satisfies equation 3548: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8d_Law3548 : Magma.searchT prn8h8d.E Law3548
    (Magma.envs 8 2) (ordprn8h8d_Law3548.map fun i ↦
      ((i, (List.finRange 8).filter (Magma.orbitOK prn8h8d.E prn8h8d.z prn8h8d.st i ·)),
        Magma.cells prn8h8d.tr i))
    (Array.replicate (8 * 8) none) = true := by
  native_decide
