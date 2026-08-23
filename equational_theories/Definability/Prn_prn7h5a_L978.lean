import equational_theories.Definability.Prn_prn7h5a_data
import equational_theories.Definability.Prune

/-! # No group of order 5 on Fin 7 invariant operation satisfies equation 978 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn7h5a group on tuples: enough to prune the
search for equation 978 exactly as hard as all `7^3` of them. -/
def envprn7h5a_Law978 : List (Array Nat) := [#[0, 0, 0], #[0, 0, 1], #[0, 0, 2], #[0, 0, 3], #[0, 0, 4], #[0, 0, 5], #[0, 0, 6], #[0, 1, 0], #[0, 1, 1], #[0, 1, 2], #[0, 1, 3], #[0, 1, 4], #[0, 1, 5], #[0, 1, 6], #[0, 2, 0], #[0, 2, 1], #[0, 2, 2], #[0, 2, 3], #[0, 2, 4], #[0, 2, 5], #[0, 2, 6], #[0, 3, 0], #[0, 3, 1], #[0, 3, 2], #[0, 3, 3], #[0, 3, 4], #[0, 3, 5], #[0, 3, 6], #[0, 4, 0], #[0, 4, 1], #[0, 4, 2], #[0, 4, 3], #[0, 4, 4], #[0, 4, 5], #[0, 4, 6], #[0, 5, 0], #[0, 5, 1], #[0, 5, 2], #[0, 5, 3], #[0, 5, 4], #[0, 5, 5], #[0, 5, 6], #[0, 6, 0], #[0, 6, 1], #[0, 6, 2], #[0, 6, 3], #[0, 6, 4], #[0, 6, 5], #[0, 6, 6], #[1, 0, 0], #[1, 0, 1], #[1, 0, 2], #[1, 0, 3], #[1, 0, 4], #[1, 0, 5], #[1, 0, 6], #[1, 1, 0], #[1, 1, 1], #[1, 1, 5], #[1, 5, 0], #[1, 5, 1], #[1, 5, 5], #[5, 0, 0], #[5, 0, 1], #[5, 0, 2], #[5, 0, 3], #[5, 0, 4], #[5, 0, 5], #[5, 0, 6], #[5, 1, 0], #[5, 1, 1], #[5, 1, 5], #[5, 5, 0], #[5, 5, 1], #[5, 5, 5]]

/-- The order the orbits of the prn7h5a family are assigned in when refuting equation
978. Any order is sound; this one was searched for. -/
def ordprn7h5a_Law978 : List (Fin 13) := [12, 2, 9, 5, 8, 0, 7, 11, 6, 1, 10, 4, 3]

/-- No prn7h5a-invariant operation on `Fin 7` satisfies equation 978: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h5a_Law978 :
    DefSearch.go 7 (Magma.toTm Law978.lhs) (Magma.toTm Law978.rhs)
      (Magma.levels prn7h5a.E prn7h5a.z prn7h5a.st prn7h5a.tr ordprn7h5a_Law978)
      (Array.replicate (7 * 7) 7) envprn7h5a_Law978 = true := by
  native_decide
