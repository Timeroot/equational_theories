import equational_theories.Definability.Prn_prn9h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 invariant operation satisfies equation 704 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h8a group on tuples: enough to prune the
search for equation 704 exactly as hard as all `9^2` of them. -/
def envprn9h8a_Law704 : List (Array Nat) := [#[0, 0], #[0, 1], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7], #[1, 8]]

/-- The order the orbits of the prn9h8a family are assigned in when refuting equation
704. Any order is sound; this one was searched for. -/
def ordprn9h8a_Law704 : List (Fin 11) := List.finRange 11

/-- No prn9h8a-invariant operation on `Fin 9` satisfies equation 704: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8a_Law704 :
    DefSearch.go 9 (Magma.toTm Law704.lhs) (Magma.toTm Law704.rhs)
      (Magma.levels prn9h8a.E prn9h8a.z prn9h8a.st prn9h8a.tr ordprn9h8a_Law704)
      (Array.replicate (9 * 9) 9) envprn9h8a_Law704 = true := by
  native_decide
