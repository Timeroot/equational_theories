import equational_theories.Definability.Prn_prn8h8a_data
import equational_theories.Definability.Prune

/-! # No group of order 8 on Fin 8 invariant operation satisfies equation 4273 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h8a group on tuples: enough to prune the
search for equation 4273 exactly as hard as all `8^2` of them. -/
def envprn8h8a_Law4273 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 4], #[0, 5], #[0, 6], #[4, 0], #[4, 1], #[4, 2], #[4, 4], #[4, 5], #[4, 6]]

/-- The order the orbits of the prn8h8a family are assigned in when refuting equation
4273. Any order is sound; this one was searched for. -/
def ordprn8h8a_Law4273 : List (Fin 12) := List.finRange 12

/-- No prn8h8a-invariant operation on `Fin 8` satisfies equation 4273: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h8a_Law4273 :
    DefSearch.go 8 (Magma.toTm Law4273.lhs) (Magma.toTm Law4273.rhs)
      (Magma.levels prn8h8a.E prn8h8a.z prn8h8a.st prn8h8a.tr ordprn8h8a_Law4273)
      (Array.replicate (8 * 8) 8) envprn8h8a_Law4273 = true := by
  native_decide
