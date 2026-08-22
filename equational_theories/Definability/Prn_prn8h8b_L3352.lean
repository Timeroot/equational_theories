import equational_theories.Definability.Prn_prn8h8b_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#2) invariant operation satisfies equation 3352 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8b family are assigned in when refuting equation
3352. Any order is sound; this one was searched for. -/
def ordprn8h8b_Law3352 : List (Fin 8) := [4, 0, 5, 6, 7, 3, 1, 2]

/-- No prn8h8b-invariant operation on `Fin 8` satisfies equation 3352: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8b_Law3352 : Magma.searchT prn8h8b.E Law3352
    (Magma.envs 8 2) (ordprn8h8b_Law3352.map fun i ↦
      ((i, (List.finRange 8).filter (Magma.orbitOK prn8h8b.E prn8h8b.z prn8h8b.st i ·)),
        Magma.cells prn8h8b.tr i))
    (Array.replicate (8 * 8) none) = true := by
  native_decide
