import equational_theories.Definability.Prn_prn9h8d_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 (#4) invariant operation satisfies equation 1279 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h8d group on tuples: enough to prune the
search for equation 1279 exactly as hard as all `9^2` of them. -/
def envprn9h8d_Law1279 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[0, 8], #[3, 0], #[3, 3]]

/-- The order the orbits of the prn9h8d family are assigned in when refuting equation
1279. Any order is sound; this one was searched for. -/
def ordprn9h8d_Law1279 : List (Fin 11) := [0, 3, 9, 10, 8, 2, 1, 7, 6, 5, 4]

/-- No prn9h8d-invariant operation on `Fin 9` satisfies equation 1279: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8d_Law1279 :
    DefSearch.go 9 (Magma.toTm Law1279.lhs) (Magma.toTm Law1279.rhs)
      (Magma.levels prn9h8d.E prn9h8d.z prn9h8d.st prn9h8d.tr ordprn9h8d_Law1279)
      (Array.replicate (9 * 9) 9) envprn9h8d_Law1279 = true := by
  native_decide
