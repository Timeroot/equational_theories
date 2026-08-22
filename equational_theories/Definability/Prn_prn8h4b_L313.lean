import equational_theories.Definability.Prn_prn8h4b_data
import equational_theories.Definability.Prune

/-! # No group of order 4 on Fin 8 (#2) invariant operation satisfies equation 313 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h4b family are assigned in when refuting equation
313. Any order is sound; this one was searched for. -/
def ordprn8h4b_Law313 : List (Fin 16) := List.finRange 16

/-- No prn8h4b-invariant operation on `Fin 8` satisfies equation 313: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h4b_Law313 : Magma.searchT prn8h4b.E Law313
    (Magma.envs 8 2) (ordprn8h4b_Law313.map fun i ↦
      ((i, (List.finRange 8).filter (Magma.orbitOK prn8h4b.E prn8h4b.z prn8h4b.st i ·)),
        Magma.cells prn8h4b.tr i))
    (Array.replicate (8 * 8) none) = true := by
  native_decide
