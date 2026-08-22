import equational_theories.Definability.Prn_prn9h8b_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 (#2) invariant operation satisfies equation 883 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h8b family are assigned in when refuting equation
883. Any order is sound; this one was searched for. -/
def ordprn9h8b_Law883 : List (Fin 11) := [4, 8, 2, 0, 9, 10, 7, 6, 1, 3, 5]

/-- No prn9h8b-invariant operation on `Fin 9` satisfies equation 883: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8b_Law883 : Magma.searchT prn9h8b.E Law883
    (Magma.envs 9 2) (ordprn9h8b_Law883.map fun i ↦
      ((i, (List.finRange 9).filter (Magma.orbitOK prn9h8b.E prn9h8b.z prn9h8b.st i ·)),
        Magma.cells prn9h8b.tr i))
    (Array.replicate (9 * 9) none) = true := by
  native_decide
