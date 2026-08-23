import equational_theories.Definability.Prn_prn9h9a_data
import equational_theories.Definability.Prune

/-! # No group of order 9 on Fin 9 invariant operation satisfies equation 313 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h9a group on tuples: enough to prune the
search for equation 313 exactly as hard as all `9^2` of them. -/
def envprn9h9a_Law313 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[0, 8]]

/-- The orbits of the prn9h9a family, as the search takes them when refuting equation
313. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn9h9a_Law313 : List (Fin 9) := List.finRange 9

/-- No prn9h9a-invariant operation on `Fin 9` satisfies equation 313: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h9a_Law313 :
    DefSearch.go 9 (Magma.toTm Law313.lhs) (Magma.toTm Law313.rhs)
      ordprn9h9a_Law313.length
      (Magma.levels prn9h9a.E prn9h9a.z prn9h9a.st prn9h9a.tr ordprn9h9a_Law313)
      (Array.replicate (9 * 9) 9) envprn9h9a_Law313 = true := by
  native_decide
