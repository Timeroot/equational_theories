import equational_theories.Definability.Shp_shp9h6s2k3_data
import equational_theories.Definability.Prune

/-! # No shape 2 shuffle on Fin 9 invariant operation satisfies equation 3482 -/

set_option maxHeartbeats 4000000

open Law Law.MagmaLaw

/-- One assignment per orbit of the shp9h6s2k3 group on tuples: enough to prune the
search for equation 3482 exactly as hard as all `9^2` of them. -/
def envshp9h6s2k3_Law3482 : List (Array Nat) := [#[0, 0], #[0, 1], #[0, 3], #[0, 4], #[0, 5], #[1, 0], #[1, 1], #[1, 2], #[1, 3], #[1, 4], #[1, 5], #[1, 6], #[1, 7], #[1, 8]]

/-- The order the orbits of the shp9h6s2k3 family are assigned in when refuting equation
3482. Any order is sound; this one was searched for. -/
def ordshp9h6s2k3_Law3482 : List (Fin 14) := List.finRange 14

/-- No shp9h6s2k3-invariant operation on `Fin 9` satisfies equation 3482: the pruned
search over the invariant family closes without ever reaching a model. -/
theorem noshp9h6s2k3_Law3482 :
    DefSearch.go 9 (Magma.toTm Law3482.lhs) (Magma.toTm Law3482.rhs)
      (Magma.levels shp9h6s2k3.E shp9h6s2k3.z shp9h6s2k3.st shp9h6s2k3.tr ordshp9h6s2k3_Law3482)
      (Array.replicate (9 * 9) 9) envshp9h6s2k3_Law3482 = true := by
  native_decide
