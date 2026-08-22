import equational_theories.Definability.Prn_prn7h5a_data
import equational_theories.Definability.Prune

/-! # No group of order 5 on Fin 7 invariant operation satisfies equation 917 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn7h5a family are assigned in when refuting equation
917. Any order is sound; this one was searched for. -/
def ordprn7h5a_Law917 : List (Fin 13) := [0, 8, 9, 10, 11, 12, 4, 3, 5, 2, 7, 6, 1]

/-- No prn7h5a-invariant operation on `Fin 7` satisfies equation 917: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h5a_Law917 : Magma.searchT prn7h5a.E Law917
    (Magma.envs 7 2) (ordprn7h5a_Law917.map fun i ↦
      ((i, (List.finRange 7).filter (Magma.orbitOK prn7h5a.E prn7h5a.z prn7h5a.st i ·)),
        Magma.cells prn7h5a.tr i))
    (Array.replicate (7 * 7) none) = true := by
  native_decide
