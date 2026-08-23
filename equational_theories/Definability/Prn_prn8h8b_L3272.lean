import equational_theories.Definability.Prn_prn8h8b_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#2) invariant operation satisfies equation 3272 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h8b group on tuples: enough to prune the
search for equation 3272 exactly as hard as all `8^2` of them. -/
def envprn8h8b_Law3272 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7]]

/-- The orbits of the prn8h8b family, as the search takes them when refuting equation
3272. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn8h8b_Law3272 : List (Fin 8) := List.finRange 8

/-- No prn8h8b-invariant operation on `Fin 8` satisfies equation 3272: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8b_Law3272 :
    DefSearch.go 8 (Magma.toTm Law3272.lhs) (Magma.toTm Law3272.rhs)
      ordprn8h8b_Law3272.length
      (Magma.levels prn8h8b.E prn8h8b.z prn8h8b.st prn8h8b.tr ordprn8h8b_Law3272)
      (Array.replicate (8 * 8) 8) envprn8h8b_Law3272 = true := by
  native_decide
