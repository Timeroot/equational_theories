import equational_theories.Parastrophes.Equation115FiniteImageObstruction
import equational_theories.Parastrophes.Equation873DivisionCalculations

/-!
# No single equation for E873's finite left-division image

The construction used for the E115 obstruction supplies more than E115:
its opposite source N(x,y)=x+A(x-y) satisfies E873. Indeed its square is
x+s, and the triangle identity gives
  y-(x+s+A(x-y)) = A²(x-y),
so E873 reduces to A³=id. This is a fact about these constructed models,
not an assertion that all E115 opposites satisfy E873.

Their left divisions are the opposites of the E115 right divisions. Thus
the same finite fragments simulate Boolean x AND NOT y. Every identity
true in all finite E873 left images holds in that Boolean magma, whose
false row is constant. No single identity, or collection of ordinary
identities, can characterize the finite image.
-/
namespace Parastrophes.Eq873FiniteImage
noncomputable section
open Law

private theorem fragments (c : Eq115BooleanTurn.Completed)
    (P : Finset (Eq115BooleanTurn.W × Eq115BooleanTurn.W))
    (S : Finset Eq115BooleanTurn.W) :
    ∃ (G : Type) (_ : Finite G) (D : Magma G) (e : Eq115BooleanTurn.W → G),
      InImage Law873.dual .right D ∧ Set.InjOn e (↑S : Set Eq115BooleanTurn.W) ∧
      ∀ p ∈ P, D.op (e p.1) (e p.2)=e (p.2-c.turn (p.1-p.2)) := by
  obtain ⟨G,hG,D,e,_,h873,hi,hp⟩ := Eq115BooleanTurn.finite_fragment_common c P S
  exact ⟨G,hG,D,e,h873,hi,hp⟩

/-- The obstruction concerns the full equational theory, not a bounded
search through possible single equations. -/
theorem boolean_theory (L : NatMagmaLaw)
    (h : ∀ (G : Type) (_hG : Finite G) (D : Magma G), InImage Law873 .left D →
      @satisfies _ G D L) :
    @satisfies _ Bool Eq873Division.booleanCounterexample L := by
  have hb := Eq115BooleanTurn.boolean_theory_from_fragments Law873.dual fragments L.dual
    (fun G hG D hi => by
      have him : InImage Law873 .left (opposite D) :=
        (inImage_dual Law873 .left (opposite D)).mp hi
      exact (satisfies_opposite (opposite D) L).mpr (h G hG (opposite D) him))
  have he : opposite Eq873Division.booleanCounterexample = Eq115RightImage.booleanCounterexample := by
    unfold opposite Eq873Division.booleanCounterexample Eq115RightImage.booleanCounterexample
    congr 1
    funext x y
    cases x <;> cases y <;> rfl
  apply (satisfies_opposite Eq873Division.booleanCounterexample L).mp
  rw [he]
  exact hb

theorem no_singleEquation : ¬ SingleEquation .fin Law873 .left := by
  rintro ⟨L,hL⟩
  apply Eq873Division.booleanCounterexample_not_image
  apply (hL Bool Eq873Division.booleanCounterexample (inferInstance : Finite Bool)).mp
  exact boolean_theory L (fun G hG D hi => (hL G D hG).mpr hi)

end
end Parastrophes.Eq873FiniteImage

namespace Parastrophes.Catalogue

/-- Opposite triangle-trade models simulate Boolean x AND NOT y, which
satisfies every identity of finite E873 left images but is not an image. -/
@[parastrophe_result] theorem left_noSingleEquation873_fin :
    ¬ SingleEquation .fin Law873 .left := Eq873FiniteImage.no_singleEquation

end Parastrophes.Catalogue
