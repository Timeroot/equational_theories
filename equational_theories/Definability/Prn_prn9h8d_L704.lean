import equational_theories.Definability.Prn_prn9h8d_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 (#4) invariant operation satisfies equation 704 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h8d family are assigned in when refuting equation
704. Any order is sound; this one was searched for. -/
def ordprn9h8d_Law704 : List (Fin 11) := [6, 3, 10, 9, 5, 0, 7, 2, 4, 8, 1]

/-- No prn9h8d-invariant operation on `Fin 9` satisfies equation 704: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8d_Law704 : Magma.searchT prn9h8d.E Law704
    (Magma.envs 9 2) (ordprn9h8d_Law704.map fun i ↦
      ((i, (List.finRange 9).filter (Magma.orbitOK prn9h8d.E prn9h8d.z prn9h8d.st i ·)),
        Magma.cells prn9h8d.tr i))
    (Array.replicate (9 * 9) none) = true := by
  native_decide
