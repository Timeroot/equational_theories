import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All

/-!
# A square-map criterion for E883's right image

We work with the opposite operation: E2744 is the dual of E883, so its left
image is the opposite of the right image in question. Write `*` for the
prospective division and `s` for the source square. The two conditions are

    y * (x * (s(x) * y)) = x,       x * (s(x) * x) = s(x).

On finite carriers these conditions are necessary and sufficient. The source
operation is recovered as `M(x,y) = y * (s(y) * x)`. No separately assumed
quasigroup condition is needed for the converse. The first condition makes
each row surjective, and finiteness supplies its inverse identity.

This is a criterion with an auxiliary unary operation, NOT a two-equation
basis in the original magma signature. Recovering s by a fixed magma term
and compressing the resulting identities remain open. No catalogue attribute
is registered here.
-/
namespace Parastrophes.Eq883RightImage
open Law

def Frame {G : Type} (D : Magma G) (s : G → G) : Prop :=
  (∀ x y, D.op y (D.op x (D.op (s x) y)) = x) ∧
  (∀ x, D.op x (D.op (s x) x) = s x)

/-- Reverse the three bijections in E2744. No finiteness is used. -/
theorem multiplication_eq {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation2744 G M) (x y : G) :
    M.op x y = D.op y (D.op (M.op y y) x) := by
  have he := h (D.op y (D.op (M.op y y) x)) y
  simpa only [hd.1] using he.symm

theorem forward {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation2744 G M) :
    Frame D (fun x => M.op x x) := by
  constructor
  · intro x y
    rw [← multiplication_eq M D hd h y x, hd.2]
  · intro x
    exact (multiplication_eq M D hd h x x).symm

/-- The recovered operation is exactly the row inverse of D. -/
theorem backward {G : Type} [Finite G] (D : Magma G) (s : G → G)
    (h : Frame D s) :
    let M : Magma G := ⟨fun x y => D.op y (D.op (s y) x)⟩
    IsDivision .left M D ∧ @Equation2744 G M ∧ (∀ x, M.op x x = s x) := by
  let M : Magma G := ⟨fun x y => D.op y (D.op (s y) x)⟩
  have dm (x y : G) : D.op x (M.op x y) = y := h.1 y x
  have hi (x : G) : Function.Injective (D.op x) :=
    Finite.injective_iff_surjective.mpr (fun y => ⟨M.op x y, dm x y⟩)
  have hd : IsDivision .left M D :=
    ⟨fun x y => hi x (dm x (D.op x y)), dm⟩
  have hs (x : G) : M.op x x = s x := h.2 x
  refine ⟨hd, ?_, hs⟩
  intro x y
  change x = M.op (M.op (M.op y y) (M.op y x)) y
  change x = D.op y (D.op (s y) (M.op (M.op y y) (M.op y x)))
  rw [hs, hd.2, hd.2]

/-- The auxiliary square is not an arbitrary extra parameter: it is unique. -/
theorem square_unique {G : Type} [Finite G] (D : Magma G)
    (s t : G → G) (hs : Frame D s) (ht : Frame D t) : s = t := by
  obtain ⟨hds, _, hss⟩ := backward D s hs
  obtain ⟨hdt, _, htt⟩ := backward D t ht
  have hm := division_unique (division_symm hds) (division_symm hdt)
  funext x
  exact (hss x).symm.trans ((congrArg (fun M : Magma G => M.op x x) hm).trans (htt x))

theorem inImage_iff {G : Type} [Finite G] (D : Magma G) :
    InImage Law2744 .left D ↔ ∃ s : G → G, Frame D s := by
  constructor
  · rintro ⟨M, hM, hd⟩
    exact ⟨fun x => M.op x x, forward M D hd ((@Law2744.models_iff G M).mp hM)⟩
  · rintro ⟨s, hs⟩
    obtain ⟨hd, hM, _⟩ := backward D s hs
    let M : Magma G := ⟨fun x y => D.op y (D.op (s y) x)⟩
    exact ⟨M, (@Law2744.models_iff G M).mpr hM, hd⟩

end Parastrophes.Eq883RightImage
