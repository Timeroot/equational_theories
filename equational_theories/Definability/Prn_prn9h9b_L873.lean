import equational_theories.Definability.Prn_prn9h9b_data
import equational_theories.Definability.Prune

/-! # No group of order 9 on Fin 9 (#2) invariant operation satisfies equation 873 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h9b group on tuples: enough to prune the
search for equation 873 exactly as hard as all `9^2` of them. -/
def envprn9h9b_Law873 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[0, 8]]

/-- The orbits of the prn9h9b family, as the search takes them when refuting equation
873. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn9h9b_Law873 : List (Fin 9) := List.finRange 9

/-- No prn9h9b-invariant operation on `Fin 9` satisfies equation 873: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h9b_Law873 :
    DefSearch.go 9 (Magma.toTm Law873.lhs) (Magma.toTm Law873.rhs)
      ordprn9h9b_Law873.length
      (Magma.levels prn9h9b.E prn9h9b.z prn9h9b.st prn9h9b.tr ordprn9h9b_Law873)
      (Array.replicate (9 * 9) 9) envprn9h9b_Law873 = true := by
  native_decide
