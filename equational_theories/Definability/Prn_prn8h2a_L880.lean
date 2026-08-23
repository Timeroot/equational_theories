import equational_theories.Definability.Prn_prn8h2a_data
import equational_theories.Definability.Prune

/-! # No group of order 2 on Fin 8 invariant operation satisfies equation 880 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn8h2a group on tuples: enough to prune the
search for equation 880 exactly as hard as all `8^2` of them. -/
def envprn8h2a_Law880 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 2], #[0, 3], #[0, 4], #[0, 5], #[0, 6], #[0, 7], #[2, 0], #[2, 1], #[2, 2], #[2, 3], #[2, 4], #[2, 5], #[2, 6], #[2, 7], #[4, 0], #[4, 1], #[4, 2], #[4, 3], #[4, 4], #[4, 5], #[4, 6], #[4, 7], #[6, 0], #[6, 1], #[6, 2], #[6, 3], #[6, 4], #[6, 5], #[6, 6], #[6, 7]]

/-- The orbits of the prn8h2a family, as the search takes them when refuting equation
880. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn8h2a_Law880 : List (Fin 32) := List.finRange 32

/-- No prn8h2a-invariant operation on `Fin 8` satisfies equation 880: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn8h2a_Law880 :
    DefSearch.go 8 (Magma.toTm Law880.lhs) (Magma.toTm Law880.rhs)
      ordprn8h2a_Law880.length
      (Magma.levels prn8h2a.E prn8h2a.z prn8h2a.st prn8h2a.tr ordprn8h2a_Law880)
      (Array.replicate (8 * 8) 8) envprn8h2a_Law880 = true := by
  native_decide
