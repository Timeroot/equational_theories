import equational_theories.Definability.Prn_prn7h5a_data
import equational_theories.Definability.Prune

/-! # No group of order 5 on Fin 7 invariant operation satisfies equation 883 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn7h5a group on tuples: enough to prune the
search for equation 883 exactly as hard as all `7^2` of them. -/
def envprn7h5a_Law883 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[1, 0], #[1, 1], #[1, 5], #[5, 0], #[5, 1], #[5, 5]]

/-- The orbits of the prn7h5a family, as the search takes them when refuting equation
883. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn7h5a_Law883 : List (Fin 13) := List.finRange 13

/-- No prn7h5a-invariant operation on `Fin 7` satisfies equation 883: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn7h5a_Law883 :
    DefSearch.go 7 (Magma.toTm Law883.lhs) (Magma.toTm Law883.rhs)
      ordprn7h5a_Law883.length
      (Magma.levels prn7h5a.E prn7h5a.z prn7h5a.st prn7h5a.tr ordprn7h5a_Law883)
      (Array.replicate (7 * 7) 7) envprn7h5a_Law883 = true := by
  native_decide
