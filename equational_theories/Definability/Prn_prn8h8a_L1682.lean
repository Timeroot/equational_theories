import equational_theories.Definability.Prn_prn8h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 invariant operation satisfies equation 1682 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8a family are assigned in when refuting equation
1682. Any order is sound; this one was searched for. -/
def ordprn8h8a_Law1682 : List (Fin 12) := [11, 8, 2, 0, 10, 6, 9, 5, 4, 1, 3, 7]

/-- No prn8h8a-invariant operation on `Fin 8` satisfies equation 1682: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8a_Law1682 : Magma.searchT prn8h8a.E Law1682
    (Magma.envs 8 2) (ordprn8h8a_Law1682.map fun i ↦
      ((i, (List.finRange 8).filter (Magma.orbitOK prn8h8a.E prn8h8a.z prn8h8a.st i ·)),
        Magma.cells prn8h8a.tr i))
    (Array.replicate (8 * 8) none) = true := by
  native_decide
