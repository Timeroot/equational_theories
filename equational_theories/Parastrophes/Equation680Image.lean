import equational_theories.Parastrophes.Equation477Image

/-!
# E680's left-division image and its two inverse cube maps

For the proposed division D, put c(x)=x*(x*x). Its exact image criterion is

    x*(y*x)=c(y),   x*c(x)=c(x)*x,   c is bijective.

This holds on arbitrary carriers. The crossed law alone makes c an
endomorphism; its bijectivity supplies both quasigroup divisions. In an
actual image c is the source's right cube `(x*x)*x`, whose inverse is the
source's left cube `x*(x*x)`. The diagonal commutation then translates back
to precisely E680, after cancelling the two inverse rows.

Bijectivity is an explicit condition, not a magma equation. In particular
this theorem does not close the single-equation characterization question,
and no characterization attribute is attached.
-/
namespace Parastrophes.Eq680Image
open Eq477Image (core)
variable {A : Type} (D : Magma A)

def Cross : Prop := ∀ x y, D.op x (D.op y x)=core D y

def Basis : Prop := Cross D ∧ ∀ x, D.op x (core D x)=D.op (core D x) x

theorem rotate (h : Cross D) (x y : A) : D.op (D.op x y) (core D x)=core D y := by
  have he := h (D.op x y) y
  rwa [h y x] at he

theorem core_endomorphism (h : Cross D) (x y : A) :
    core D (D.op x y)=D.op (core D x) (core D y) := by
  have he := rotate D h y (D.op x y)
  rw [h y x] at he
  exact he.symm

theorem core_injective (h : Cross D) (hi : ∀ x, Function.Injective (D.op x)) :
    Function.Injective (core D) := by
  intro a b hab
  have rows (t) : D.op a t=D.op b t := by
    apply hi t
    rw [h,h,hab]
  apply hi a
  apply hi a
  calc
    D.op a (D.op a a) = core D b := hab
    _ = D.op a (D.op a b) := by
      change D.op b (D.op b b)=_
      rw [← rows b,← rows (D.op a b)]

/-- Bijectivity of the cubic map supplies both divisions, without finiteness. -/
theorem quasigroup (h : Cross D) (hc : Function.Bijective (core D)) : IsQuasigroup D := by
  have rows (x) : Function.Injective (D.op x) := by
    intro y z he
    apply hc.1
    rw [← rotate D h x y,← rotate D h x z,he]
  constructor
  · intro x
    refine ⟨rows x,?_⟩
    intro y
    obtain ⟨z,rfl⟩ := hc.2 y
    exact ⟨D.op z x,h x z⟩
  · intro x
    constructor
    · intro y z he
      change D.op y x=D.op z x at he
      apply hc.1
      rw [← h x y,← h x z,he]
    · intro y
      obtain ⟨z,hz⟩ := hc.2 (D.op x y)
      exact ⟨z,rows x ((h x z).trans hz)⟩

variable (M : Magma A)

theorem division_formula (hd : IsDivision .left M D) (h : @Equation680 A M) (x y : A) :
    D.op x y=M.op y (M.op (M.op x x) x) := by
  have he := congrArg (D.op x) (h y x)
  rw [hd.2] at he
  exact he

theorem translated (hd : IsDivision .left M D) (h : @Equation680 A M) (x y : A) :
    D.op x (D.op y x)=M.op (M.op y y) y := by
  rw [division_formula D M hd h y x,hd.2]

theorem core_eq (hd : IsDivision .left M D) (h : @Equation680 A M) (x : A) :
    core D x=M.op (M.op x x) x := translated D M hd h x x

theorem forward_cross (hd : IsDivision .left M D) (h : @Equation680 A M) : Cross D := by
  intro x y
  rw [translated D M hd h,core_eq D M hd h]

/-- Two crossed rotations express the cubic map of a source product. -/
theorem core_source_product (hd : IsDivision .left M D) (h : @Equation680 A M)
    (x y : A) : core D (M.op x y)=D.op y (core D x) := by
  have hc := forward_cross D M hd h
  have first : D.op (M.op x y) y=core D x := by
    have he := hc (M.op x y) x
    rwa [hd.2] at he
  have he := hc y (M.op x y)
  rw [first] at he
  exact he.symm

theorem forward (hd : IsDivision .left M D) (h : @Equation680 A M) : Basis D := by
  refine ⟨forward_cross D M hd h,?_⟩
  intro x
  have first : D.op (M.op x x) (core D x)=x := by
    rw [core_eq D M hd h,hd.2]
  have he := forward_cross D M hd h (core D x) (M.op x x)
  rw [first,core_source_product D M hd h] at he
  exact he.symm

/-- Source left and right cubes are inverse maps. Consequently the image's
cubic map is bijective even on an infinite carrier. -/
theorem core_bijective (hd : IsDivision .left M D) (h : @Equation680 A M) :
    Function.Bijective (core D) := by
  refine ⟨core_injective D (forward_cross D M hd h)
    (fun x => (sideQuasigroup_of_division (division_symm hd) x).1),?_⟩
  intro x
  refine ⟨M.op x (M.op x x),?_⟩
  rw [core_source_product D M hd h,core_eq D M hd h,hd.2]

/-- The two bracketings of the source cube are mutually inverse, conditional
only on existence of left division. They are not the two cube maps of D. -/
theorem source_cubes_inverse (hd : IsDivision .left M D) (h : @Equation680 A M) :
    Function.LeftInverse (fun x => M.op x (M.op x x)) (fun x => M.op (M.op x x) x) ∧
    Function.RightInverse (fun x => M.op x (M.op x x)) (fun x => M.op (M.op x x) x) := by
  have hc (x) : core D (M.op x (M.op x x)) = x := by
    rw [core_source_product D M hd h, core_eq D M hd h, hd.2]
  constructor
  · intro x
    apply (core_bijective D M hd h).1
    rw [hc, core_eq D M hd h]
  · intro x
    change M.op (M.op (M.op x (M.op x x)) (M.op x (M.op x x)))
      (M.op x (M.op x x)) = x
    rw [← core_eq D M hd h, hc]

/-- The diagonal commutation translates exactly into E680 after division.
No size-dependent period or finite model is used. -/
theorem backward (hd : IsDivision .left M D) (h : Basis D)
    (hs : Function.Surjective (core D)) : @Equation680 A M := by
  have formula (x y) : M.op x (core D y)=D.op y x := by
    have he := congrArg (M.op x) (h.1 x y)
    rw [hd.1] at he
    exact he.symm
  have cube (x) : M.op (M.op x x) x=core D x := by
    obtain ⟨y,rfl⟩ := hs x
    rw [formula,formula,h.2,h.1]
  intro x y
  rw [cube,formula,hd.1]

/-- An exact conditional criterion, not a single-equation characterization. -/
theorem inImage_iff : InImage Law680 .left D ↔ Basis D ∧ Function.Bijective (core D) := by
  constructor
  · rintro ⟨M,hm,hd⟩
    have h := (@Law680.models_iff A M).mp hm
    exact ⟨forward D M hd h,core_bijective D M hd h⟩
  · rintro ⟨h,hc⟩
    classical
    have hq := quasigroup D h.1 hc
    let e (x : A) := Equiv.ofBijective (D.op x) (hq.1 x)
    let M : Magma A := ⟨fun x y => (e x).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (e x).symm_apply_apply y,fun x y => (e x).apply_symm_apply y⟩
    exact ⟨M,(@Law680.models_iff A M).mpr (backward D M hd h hc.2),hd⟩

/-- On finite carriers the explicit extra condition can be just injectivity
of the cubic map. Neither of the two identities asserts that condition. -/
theorem inImage_iff_core_injective [Finite A] :
    InImage Law680 .left D ↔ Basis D ∧ Function.Injective (core D) := by
  rw [inImage_iff D]
  exact ⟨fun h => ⟨h.1, h.2.1⟩,
    fun h => ⟨h.1, h.2, Finite.surjective_of_injective h.2⟩⟩

end Parastrophes.Eq680Image
