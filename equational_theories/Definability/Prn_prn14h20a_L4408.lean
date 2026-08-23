import equational_theories.Definability.Prn_prn14h20a_data
import equational_theories.Definability.Prune

/-! # No group of order 20 on Fin 14 invariant operation satisfies equation 4408 -/

set_option maxHeartbeats 1000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the prn14h20a group on tuples: enough to prune the
search for equation 4408 exactly as hard as all `14^2` of them. -/
def envprn14h20a_Law4408 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 4], #[0, 5], #[0, 11], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 6], #[1, 7], #[1, 8], #[1, 9], #[1, 10], #[1, 12], #[1, 13], #[4, 0], #[4, 1], #[4, 4], #[4, 5], #[4, 11]]

/-- The orbits of the prn14h20a family, as the search takes them when refuting equation
4408. This is a set, not an order: the kernel picks which one to branch on at each
node. -/
def ordprn14h20a_Law4408 : List (Fin 22) := List.finRange 22

/-- No prn14h20a-invariant operation on `Fin 14` satisfies equation 4408: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noprn14h20a_Law4408 :
    DefSearch.go 14 (Magma.toTm Law4408.lhs) (Magma.toTm Law4408.rhs)
      ordprn14h20a_Law4408.length
      (Magma.levels prn14h20a.E prn14h20a.z prn14h20a.st prn14h20a.tr ordprn14h20a_Law4408)
      (Array.replicate (14 * 14) 14) envprn14h20a_Law4408 = true := by
  native_decide
