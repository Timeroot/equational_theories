import equational_theories.Definability.Prn_prn8h4b_data
import equational_theories.Definability.Prune

/-! # No group of order 4 on Fin 8 (#2) invariant operation satisfies equation 313 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h4b group on tuples: enough to prune the
search for equation 313 exactly as hard as all `8^2` of them. -/
def envprn8h4b_Law313 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7]]

/-- The order the orbits of the prn8h4b family are assigned in when refuting equation
313. Any order is sound; this one was searched for. -/
def ordprn8h4b_Law313 : List (Fin 16) := List.finRange 16

/-- No prn8h4b-invariant operation on `Fin 8` satisfies equation 313: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h4b_Law313 :
    DefSearch.go 8 (Magma.toTm Law313.lhs) (Magma.toTm Law313.rhs)
      (Magma.levels prn8h4b.E prn8h4b.z prn8h4b.st prn8h4b.tr ordprn8h4b_Law313)
      (Array.replicate (8 * 8) 8) envprn8h4b_Law313 = true := by
  native_decide
