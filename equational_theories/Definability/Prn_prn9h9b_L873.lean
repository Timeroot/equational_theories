import equational_theories.Definability.Prn_prn9h9b_data
import equational_theories.Definability.Prune

/-! # No group of order 9 on Fin 9 (#2) invariant operation satisfies equation 873 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- The order the orbits of the prn9h9b family are assigned in when refuting equation
873. Any order is sound; this one was searched for. -/
def ordprn9h9b_Law873 : List (Fin 9) := [1, 6, 0, 5, 3, 7, 2, 4, 8]

/-- No prn9h9b-invariant operation on `Fin 9` satisfies equation 873: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h9b_Law873 : Magma.searchT prn9h9b.E Law873
    (Magma.envs 9 2) (ordprn9h9b_Law873.map fun i ↦
      ((i, (List.finRange 9).filter (Magma.orbitOK prn9h9b.E prn9h9b.z prn9h9b.st i ·)),
        Magma.cells prn9h9b.tr i))
    (Array.replicate (9 * 9) none) = true := by
  native_decide
