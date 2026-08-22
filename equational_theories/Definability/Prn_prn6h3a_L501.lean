import equational_theories.Definability.Prn_prn6h3a_data
import equational_theories.Definability.Prune

/-! # No group of order 3 on Fin 6 invariant operation satisfies equation 501 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn6h3a family are assigned in when refuting equation
501. Any order is sound; this one was searched for. -/
def ordprn6h3a_Law501 : List (Fin 12) := List.finRange 12

/-- No prn6h3a-invariant operation on `Fin 6` satisfies equation 501: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn6h3a_Law501 : Magma.searchT prn6h3a.E Law501
    (Magma.envs 6 2) (ordprn6h3a_Law501.map fun i ↦
      ((i, (List.finRange 6).filter (Magma.orbitOK prn6h3a.E prn6h3a.z prn6h3a.st i ·)),
        Magma.cells prn6h3a.tr i))
    (Array.replicate (6 * 6) none) = true := by
  native_decide
