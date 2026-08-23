import equational_theories.Definability.Prn_prn7h6a_data
import equational_theories.Definability.Prune

/-! # No group of order 6 on Fin 7 invariant operation satisfies equation 1076 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn7h6a group on tuples: enough to prune the
search for equation 1076 exactly as hard as all `7^2` of them. -/
def envprn7h6a_Law1076 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[6, 0], #[6, 6]]

/-- The orbits of the prn7h6a family, as the search takes them when refuting equation
1076. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn7h6a_Law1076 : List (Fin 9) := List.finRange 9

/-- No prn7h6a-invariant operation on `Fin 7` satisfies equation 1076: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h6a_Law1076 :
    DefSearch.go 7 (Magma.toTm Law1076.lhs) (Magma.toTm Law1076.rhs)
      ordprn7h6a_Law1076.length
      (Magma.levels prn7h6a.E prn7h6a.z prn7h6a.st prn7h6a.tr ordprn7h6a_Law1076)
      (Array.replicate (7 * 7) 7) envprn7h6a_Law1076 = true := by
  native_decide
