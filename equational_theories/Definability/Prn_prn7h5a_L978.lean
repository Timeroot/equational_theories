import equational_theories.Definability.Prn_prn7h5a_data
import equational_theories.Definability.Prune

/-! # No group of order 5 on Fin 7 invariant operation satisfies equation 978 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn7h5a family are assigned in when refuting equation
978. Any order is sound; this one was searched for. -/
def ordprn7h5a_Law978 : List (Fin 13) := [12, 2, 9, 5, 8, 0, 7, 11, 6, 1, 10, 4, 3]

/-- No prn7h5a-invariant operation on `Fin 7` satisfies equation 978: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h5a_Law978 : Magma.searchT prn7h5a.E Law978
    (Magma.envs 7 3) (ordprn7h5a_Law978.map fun i ↦
      ((i, (List.finRange 7).filter (Magma.orbitOK prn7h5a.E prn7h5a.z prn7h5a.st i ·)),
        Magma.cells prn7h5a.tr i))
    (Array.replicate (7 * 7) none) = true := by
  native_decide
