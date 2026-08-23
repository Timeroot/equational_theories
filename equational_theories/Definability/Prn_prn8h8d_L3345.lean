import equational_theories.Definability.Prn_prn8h8d_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 (#4) invariant operation satisfies equation 3345 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h8d group on tuples: enough to prune the
search for equation 3345 exactly as hard as all `8^2` of them. -/
def envprn8h8d_Law3345 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7]]

/-- The orbits of the prn8h8d family, as the search takes them when refuting equation
3345. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn8h8d_Law3345 : List (Fin 8) := List.finRange 8

/-- No prn8h8d-invariant operation on `Fin 8` satisfies equation 3345: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8d_Law3345 :
    DefSearch.go 8 (Magma.toTm Law3345.lhs) (Magma.toTm Law3345.rhs)
      ordprn8h8d_Law3345.length
      (Magma.levels prn8h8d.E prn8h8d.z prn8h8d.st prn8h8d.tr ordprn8h8d_Law3345)
      (Array.replicate (8 * 8) 8) envprn8h8d_Law3345 = true := by
  native_decide
