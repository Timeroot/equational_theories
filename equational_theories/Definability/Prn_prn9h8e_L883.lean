import equational_theories.Definability.Prn_prn9h8e_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 (#5) invariant operation satisfies equation 883 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h8e family are assigned in when refuting equation
883. Any order is sound; this one was searched for. -/
def ordprn9h8e_Law883 : List (Fin 11) := [2, 10, 5, 7, 1, 0, 3, 9, 6, 8, 4]

/-- No prn9h8e-invariant operation on `Fin 9` satisfies equation 883: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8e_Law883 : Magma.searchT prn9h8e.E Law883
    (Magma.envs 9 2) (ordprn9h8e_Law883.map fun i ↦
      ((i, (List.finRange 9).filter (Magma.orbitOK prn9h8e.E prn9h8e.z prn9h8e.st i ·)),
        Magma.cells prn9h8e.tr i))
    (Array.replicate (9 * 9) none) = true := by
  native_decide
