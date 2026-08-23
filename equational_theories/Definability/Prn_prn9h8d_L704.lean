import equational_theories.Definability.Prn_prn9h8d_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 (#4) invariant operation satisfies equation 704 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h8d group on tuples: enough to prune the
search for equation 704 exactly as hard as all `9^2` of them. -/
def envprn9h8d_Law704 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[0, 8], #[3, 0], #[3, 3]]

/-- The orbits of the prn9h8d family, as the search takes them when refuting equation
704. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn9h8d_Law704 : List (Fin 11) := List.finRange 11

/-- No prn9h8d-invariant operation on `Fin 9` satisfies equation 704: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8d_Law704 :
    DefSearch.go 9 (Magma.toTm Law704.lhs) (Magma.toTm Law704.rhs)
      ordprn9h8d_Law704.length
      (Magma.levels prn9h8d.E prn9h8d.z prn9h8d.st prn9h8d.tr ordprn9h8d_Law704)
      (Array.replicate (9 * 9) 9) envprn9h8d_Law704 = true := by
  native_decide
