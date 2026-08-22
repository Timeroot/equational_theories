import equational_theories.Definability.Prn_prn8h8c_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#3) invariant operation satisfies equation 3345 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn8h8c family are assigned in when refuting equation
3345. Any order is sound; this one was searched for. -/
def ordprn8h8c_Law3345 : List (Fin 8) := [4, 2, 6, 7, 5, 0, 1, 3]

/-- No prn8h8c-invariant operation on `Fin 8` satisfies equation 3345: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8c_Law3345 : Magma.searchT prn8h8c.E Law3345
    (Magma.envs 8 2) (ordprn8h8c_Law3345.map fun i ↦
      ((i, (List.finRange 8).filter (Magma.orbitOK prn8h8c.E prn8h8c.z prn8h8c.st i ·)),
        Magma.cells prn8h8c.tr i))
    (Array.replicate (8 * 8) none) = true := by
  native_decide
