import equational_theories.Parastrophes.RotatedImages
import equational_theories.Parastrophes.FiniteSolutions
import equational_theories.ManuallyProved.Equation677

/-!
# The finite E677 → E255 problem in left-division coordinates

E9321 is the exact finite left-division image of E677. Within this
correspondence, E255 becomes E203. The candidate fixer of `x` is the
short term `x * (x*x)` in the new operation.
-/
namespace Parastrophes.Eq9321
open Law FreeMagma

/-- Inverting a row of E9321 recovers the E677 multiplication by this term. -/
theorem left_term : UniformTermWitness .fin leftImage677 .left
    ((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))) := by
  apply uniform_left_of_solution
  intro G M h x y
  exact ((leftImage677_iff M).mp h y x).symm

/-- Different elements index different rows, even without finiteness. -/
theorem rows_injective {G : Type} (D : Magma G)
    (hD : @satisfies _ G D leftImage677) : Function.Injective D.op := by
  have h := (leftImage677_iff D).mp hD
  intro a b hab
  calc
    a = D.op a (D.op (D.op a a) (D.op a (D.op a a))) := h a a
    _ = D.op a (D.op (D.op b a) (D.op b (D.op b a))) := by rw [hab]
    _ = b := (h b a).symm

/-- Left division preserves exactly which row permutations fix a point. -/
theorem fixer_iff {G : Type} (M D : Magma G) (hd : IsDivision .left M D) (x y : G) :
    M.op y x = x ↔ D.op y x = x := by
  constructor
  · intro h
    exact (congrArg (D.op y) h).symm.trans (hd.2 y x)
  · intro h
    exact (congrArg (M.op y) h).symm.trans (hd.1 y x)

/-- E677 identifies its cubic left-associated power with the new
right-associated cubic power. This calculation does not use finiteness. -/
theorem cubic_transfer {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation677 G M) (x : G) :
    D.op x (D.op x x) = M.op (M.op x x) x := by
  have he := congrArg (fun v => D.op x (D.op x v)) (h x x)
  simpa only [hd.2] using he

/-- The E255 condition at one point is exactly E203 in the division operation. -/
theorem equation255_at_iff203 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation677 G M) (x : G) :
    x = M.op (M.op (M.op x x) x) x ↔ x = D.op (D.op x (D.op x x)) x := by
  rw [cubic_transfer M D hd h x]
  exact ⟨fun he => ((fixer_iff M D hd x _).mp he.symm).symm,
    fun he => ((fixer_iff M D hd x _).mpr he.symm).symm⟩

theorem equation255_iff203 {G : Type} (M D : Magma G)
    (hd : IsDivision .left M D) (h : @Equation677 G M) :
    @Equation255 G M ↔ @Equation203 G D :=
  ⟨fun hp x => (equation255_at_iff203 M D hd h x).mp (hp x),
    fun hp x => (equation255_at_iff203 M D hd h x).mpr (hp x)⟩

/-- A finite E9321 model has at most one row fixing a specified point,
and its label must be `x * (x*x)`. Existence remains the open question. -/
theorem fixer_unique {G : Type} [Finite G] (D : Magma G)
    (hD : @satisfies _ G D leftImage677) {x y : G} (hy : D.op y x = x) :
    y = D.op x (D.op x x) := by
  obtain ⟨M, hM, hd⟩ := (Catalogue.left_characterizes677_fin_long G D
    (inferInstance : Finite G)).mp hD
  have h := (@Law677.models_iff G M).mp hM
  rw [cubic_transfer M D hd h]
  exact @Eq677.eq677_fixer_unique G M _ h x y ((fixer_iff M D hd x y).mpr hy)

/-- E203 holds at `x` exactly when some row fixes `x`. -/
theorem equation203_at_iff_fixer {G : Type} [Finite G] (D : Magma G)
    (hD : @satisfies _ G D leftImage677) (x : G) :
    x = D.op (D.op x (D.op x x)) x ↔ ∃ y, D.op y x = x := by
  constructor
  · intro h
    exact ⟨D.op x (D.op x x), h.symm⟩
  · rintro ⟨y, hy⟩
    rw [← fixer_unique D hD hy]
    exact hy.symm

/-- Bijective columns suffice for the E203 conclusion. They are not
necessary: the imported 25- and 49-element models have column collisions. -/
theorem equation203_of_rightQuasigroup {G : Type} [Finite G] (D : Magma G)
    (hD : @satisfies _ G D leftImage677) (hq : IsSideQuasigroup .right D) :
    @Equation203 G D := by
  intro x
  exact (equation203_at_iff_fixer D hD x).mpr ((hq x).2 x)

/-- On each finite carrier, the two proposed implications are equivalent. -/
theorem finite_question_equiv (G : Type) [Finite G] :
    (∀ M : Magma G, @Equation677 G M → @Equation255 G M) ↔
    (∀ D : Magma G, @satisfies _ G D leftImage677 → @Equation203 G D) := by
  constructor
  · intro h D hD
    obtain ⟨M, hM, hd⟩ := (Catalogue.left_characterizes677_fin_long G D
      (inferInstance : Finite G)).mp hD
    have hm := (@Law677.models_iff G M).mp hM
    exact (equation255_iff203 M D hd hm).mp (h M hm)
  · intro h M hM
    let D := termMagma M (Lf 1 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 0))
    have hm := (@Law677.models_iff G M).mpr hM
    have hd : IsDivision .left M D := Catalogue.left_term677_fin G M
      (inferInstance : Finite G) hm
    have hD := (Catalogue.left_characterizes677_fin_long G D
      (inferInstance : Finite G)).mpr ⟨M, hm, hd⟩
    exact (equation255_iff203 M D hd hM).mpr (h D hD)

end Parastrophes.Eq9321
