import equational_theories.Definability.Prn_prn9h8e_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 9 (#5) invariant operation satisfies equation 883 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn9h8e group on tuples: enough to prune the
search for equation 883 exactly as hard as all `9^2` of them. -/
def envprn9h8e_Law883 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[0, 8], #[1, 0], #[1, 1]]

/-- The order the orbits of the prn9h8e family are assigned in when refuting equation
883. Any order is sound; this one was searched for. -/
def ordprn9h8e_Law883 : List (Fin 11) := [2, 10, 5, 7, 1, 0, 3, 9, 6, 8, 4]

/-- No prn9h8e-invariant operation on `Fin 9` satisfies equation 883: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn9h8e_Law883 :
    DefSearch.go 9 (Magma.toTm Law883.lhs) (Magma.toTm Law883.rhs)
      (Magma.levels prn9h8e.E prn9h8e.z prn9h8e.st prn9h8e.tr ordprn9h8e_Law883)
      (Array.replicate (9 * 9) 9) envprn9h8e_Law883 = true := by
  native_decide
