import equational_theories.Definability.Prn_prn9h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 invariant operation satisfies equation 1279 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h8a family are assigned in when refuting equation
1279. Any order is sound; this one was searched for. -/
def ordprn9h8a_Law1279 : List (Fin 11) := [2, 1, 7, 3, 6, 0, 9, 5, 8, 10, 4]

/-- No prn9h8a-invariant operation on `Fin 9` satisfies equation 1279: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8a_Law1279 : Magma.searchT prn9h8a.E Law1279
    (Magma.envs 9 2) (ordprn9h8a_Law1279.map fun i ↦
      ((i, (List.finRange 9).filter (Magma.orbitOK prn9h8a.E prn9h8a.z prn9h8a.st i ·)),
        Magma.cells prn9h8a.tr i))
    (Array.replicate (9 * 9) none) = true := by
  native_decide
