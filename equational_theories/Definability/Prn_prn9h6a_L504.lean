import equational_theories.Definability.Prn_prn9h6a_data
import equational_theories.Definability.Prune

/-! # No group of order 6 on Fin 9 invariant operation satisfies equation 504 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h6a family are assigned in when refuting equation
504. Any order is sound; this one was searched for. -/
def ordprn9h6a_Law504 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No prn9h6a-invariant operation on `Fin 9` satisfies equation 504: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h6a_Law504 : Magma.searchT prn9h6a.E Law504
    (Magma.envs 9 2) (ordprn9h6a_Law504.map fun i ↦
      ((i, (List.finRange 9).filter (Magma.orbitOK prn9h6a.E prn9h6a.z prn9h6a.st i ·)),
        Magma.cells prn9h6a.tr i))
    (Array.replicate (9 * 9) none) = true := by
  native_decide
