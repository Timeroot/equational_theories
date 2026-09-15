import equational_theories.Spectrum.BitTables
import equational_theories.Equations.All
import equational_theories.Generated.VampireProven.Proofs11

/-! Mathematical preprocessing for the bit-vector exclusions. -/
namespace Spectrum.BitExclusion

theorem left_injective_474 {G : Type*} [Finite G] (M : Magma G)
    (h : @Equation474 G M) (y : G) : Function.Injective (M.op y) := by
  apply Finite.injective_iff_surjective.mpr
  intro x
  exact ⟨M.op x (M.op y (M.op x y)), (h x y).symm⟩

theorem left_injective_1286 {G : Type*} [Finite G] (M : Magma G)
    (h : @Equation1286 G M) (y : G) : Function.Injective (M.op y) := by
  apply Finite.injective_iff_surjective.mpr
  intro x
  exact ⟨M.op (M.op (M.op x y) x) y, (h x y).symm⟩

theorem unary_474 {G : Type*} (M : Magma G) (h : @Equation474 G M) (x : G) :
    M.op x (M.op x x) = x :=
  (@Equation474_implies_Equation8 G M h x).symm

end Spectrum.BitExclusion
