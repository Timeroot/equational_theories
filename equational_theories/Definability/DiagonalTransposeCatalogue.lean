import equational_theories.Definability.DiagonalTranspose
open Law Law.MagmaLaw DiagonalTranspose

/-! A reversible FO companion obtained by transposing precisely the pairs
whose squares differ. This adds a target law without losing the source table. -/
namespace DiagonalTransposeCatalogue
private theorem target_3545_3253 {G : Type} (M : Magma G) (h : @Equation3545 G M) :
    @Equation3253 G ((forward (.eq 2 3)).magma M) := by
  classical
  intro x
  simp [DiagonalTranspose.forward_apply, DiagonalTranspose.guard, DiagonalTranspose.holds, DiagonalOutputSwap.value]
  all_goals unfold Equation3545 at h; grind

theorem Equation3253_structuralFrom_Equation3545 : Law3253.StructuralFrom Law3545 :=
  structuralFrom_diagonalTranspose (.eq 2 3) (fun M h =>
    (@Law3253.models_iff _ ((forward (.eq 2 3)).magma M)).mpr
      (target_3545_3253 M ((@Law3545.models_iff _ M).mp h)))

/-- info: 'DiagonalTransposeCatalogue.Equation3253_structuralFrom_Equation3545' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3253_structuralFrom_Equation3545
end DiagonalTransposeCatalogue
