import equational_theories.Definability.Prn_prn7h6a_data
import equational_theories.Definability.Prune

/-! # No group of order 6 on Fin 7 invariant operation satisfies equation 1076 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn7h6a family are assigned in when refuting equation
1076. Any order is sound; this one was searched for. -/
def ordprn7h6a_Law1076 : List (Fin 9) := [6, 8, 5, 3, 2, 0, 4, 1, 7]

/-- No prn7h6a-invariant operation on `Fin 7` satisfies equation 1076: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h6a_Law1076 : Magma.searchT prn7h6a.E Law1076
    (Magma.envs 7 2) (ordprn7h6a_Law1076.map fun i ↦
      ((i, (List.finRange 7).filter (Magma.orbitOK prn7h6a.E prn7h6a.z prn7h6a.st i ·)),
        Magma.cells prn7h6a.tr i))
    (Array.replicate (7 * 7) none) = true := by
  native_decide
