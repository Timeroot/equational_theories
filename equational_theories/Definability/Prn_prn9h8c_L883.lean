import equational_theories.Definability.Prn_prn9h8c_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 (#3) invariant operation satisfies equation 883 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h8c group on tuples: enough to prune the
search for equation 883 exactly as hard as all `9^2` of them. -/
def envprn9h8c_Law883 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[0, 8], #[8, 0], #[8, 8]]

/-- The orbits of the prn9h8c family, as the search takes them when refuting equation
883. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn9h8c_Law883 : List (Fin 11) := List.finRange 11

/-- No prn9h8c-invariant operation on `Fin 9` satisfies equation 883: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8c_Law883 :
    DefSearch.go 9 (Magma.toTm Law883.lhs) (Magma.toTm Law883.rhs)
      ordprn9h8c_Law883.length
      (Magma.levels prn9h8c.E prn9h8c.z prn9h8c.st prn9h8c.tr ordprn9h8c_Law883)
      (Array.replicate (9 * 9) 9) envprn9h8c_Law883 = true := by
  native_decide
