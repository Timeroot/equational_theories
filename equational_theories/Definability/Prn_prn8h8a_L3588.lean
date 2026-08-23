import equational_theories.Definability.Prn_prn8h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 invariant operation satisfies equation 3588 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h8a group on tuples: enough to prune the
search for equation 3588 exactly as hard as all `8^3` of them. -/
def envprn8h8a_Law3588 : List (Array Nat) := [#[0, 0, 0], #[0, 0, 1], #[0, 0, 2], #[0, 0, 4], #[0, 0, 5], #[0, 0, 6], #[0, 1, 0], #[0, 1, 1], #[0, 1, 2], #[0, 1, 3], #[0, 1, 4], #[0, 1, 5], #[0, 1, 6], #[0, 1, 7], #[0, 2, 0], #[0, 2, 1], #[0, 2, 2], #[0, 2, 4], #[0, 2, 5], #[0, 2, 6], #[0, 4, 0], #[0, 4, 1], #[0, 4, 2], #[0, 4, 4], #[0, 4, 5], #[0, 4, 6], #[0, 5, 0], #[0, 5, 1], #[0, 5, 2], #[0, 5, 3], #[0, 5, 4], #[0, 5, 5], #[0, 5, 6], #[0, 5, 7], #[0, 6, 0], #[0, 6, 1], #[0, 6, 2], #[0, 6, 4], #[0, 6, 5], #[0, 6, 6], #[4, 0, 0], #[4, 0, 1], #[4, 0, 2], #[4, 0, 4], #[4, 0, 5], #[4, 0, 6], #[4, 1, 0], #[4, 1, 1], #[4, 1, 2], #[4, 1, 3], #[4, 1, 4], #[4, 1, 5], #[4, 1, 6], #[4, 1, 7], #[4, 2, 0], #[4, 2, 1], #[4, 2, 2], #[4, 2, 4], #[4, 2, 5], #[4, 2, 6], #[4, 4, 0], #[4, 4, 1], #[4, 4, 2], #[4, 4, 4], #[4, 4, 5], #[4, 4, 6], #[4, 5, 0], #[4, 5, 1], #[4, 5, 2], #[4, 5, 3], #[4, 5, 4], #[4, 5, 5], #[4, 5, 6], #[4, 5, 7], #[4, 6, 0], #[4, 6, 1], #[4, 6, 2], #[4, 6, 4], #[4, 6, 5], #[4, 6, 6]]

/-- The orbits of the prn8h8a family, as the search takes them when refuting equation
3588. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn8h8a_Law3588 : List (Fin 12) := List.finRange 12

/-- No prn8h8a-invariant operation on `Fin 8` satisfies equation 3588: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8a_Law3588 :
    DefSearch.go 8 (Magma.toTm Law3588.lhs) (Magma.toTm Law3588.rhs)
      ordprn8h8a_Law3588.length
      (Magma.levels prn8h8a.E prn8h8a.z prn8h8a.st prn8h8a.tr ordprn8h8a_Law3588)
      (Array.replicate (8 * 8) 8) envprn8h8a_Law3588 = true := by
  native_decide
