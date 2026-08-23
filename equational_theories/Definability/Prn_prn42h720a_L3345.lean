import equational_theories.Definability.Prn_prn42h720a_data
import equational_theories.Definability.Prune

/-! # No group of order 720 on Fin 42 invariant operation satisfies equation 3345 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn42h720a group on tuples: enough to prune the
search for equation 3345 exactly as hard as all `42^2` of them. -/
def envprn42h720a_Law3345 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 6], #[0, 7], #[0, 12], #[0, 13], #[0, 14], #[6, 0], #[6, 1], #[6, 6], #[6, 7], #[6, 12], #[6, 13], #[6, 14], #[7, 0], #[7, 1], #[7, 2], #[7, 6], #[7, 7], #[7, 8], #[7, 12], #[7, 13], #[7, 14], #[7, 18], #[7, 19], #[7, 20], #[7, 21]]

/-- The orbits of the prn42h720a family, as the search takes them when refuting equation
3345. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn42h720a_Law3345 : List (Fin 27) := List.finRange 27

/-- No prn42h720a-invariant operation on `Fin 42` satisfies equation 3345: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn42h720a_Law3345 :
    DefSearch.go 42 (Magma.toTm Law3345.lhs) (Magma.toTm Law3345.rhs)
      ordprn42h720a_Law3345.length
      (Magma.levels prn42h720a.E prn42h720a.z prn42h720a.st prn42h720a.tr ordprn42h720a_Law3345)
      (Array.replicate (42 * 42) 42) envprn42h720a_Law3345 = true := by
  native_decide
