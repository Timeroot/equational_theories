import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All

/-!
# E115's right-division image among right quasigroups

The exact conditional characterization is E221: x=(y*(x*y))*x.
For c(x)=x*(x*x), column cancellation gives y*(x*y)=c(x).
Rotating this identity gives (x*y)*c(x)=c(y), from which c is injective
and preserves multiplication. Thus c is an automorphism on finite carriers.
In an actual image c is exactly the square map of the source operation.

The right-quasigroup hypothesis is essential. Boolean NOT x AND y satisfies
E221 and the crossed identity but is not an image. No single-equation
characterization attribute is attached to these conditional statements.
-/
namespace Parastrophes.Eq115RightImage

def core {G : Type*} (D : Magma G) (x : G) := D.op x (D.op x x)

def Common {G : Type*} (D : Magma G) : Prop :=
  ∀ x y, D.op y (D.op x y) = core D x

theorem rotate {G : Type*} (D : Magma G) (h : Common D) (x y : G) :
    D.op (D.op x y) (core D x) = core D y := by
  have he := h y (D.op x y)
  rwa [h x y] at he

theorem core_injective {G : Type*} (D : Magma G)
    (hq : IsSideQuasigroup .right D) (h : Common D) :
    Function.Injective (core D) := by
  intro x y he
  apply (hq x).1
  apply (hq (core D x)).1
  exact (rotate D h x x).trans (by simpa only [he] using (rotate D h y x).symm)

theorem left_injective {G : Type*} (D : Magma G)
    (hq : IsSideQuasigroup .right D) (h : Common D) (a : G) :
    Function.Injective (D.op a) := by
  intro x y he
  obtain ⟨u, rfl⟩ := (hq a).2 x
  obtain ⟨v, rfl⟩ := (hq a).2 y
  have hu : core D u = core D v := (h u a).symm.trans (he.trans (h v a))
  exact congrArg (fun z => D.op z a) (core_injective D hq h hu)

theorem core_mul {G : Type*} (D : Magma G)
    (hq : IsSideQuasigroup .right D) (h : Common D) (x y : G) :
    core D (D.op x y) = D.op (core D x) (core D y) := by
  apply left_injective D hq h (core D y)
  have he := rotate D h (D.op x y) (core D x)
  rw [rotate D h x y] at he
  exact he.trans (h (core D x) (core D y)).symm

theorem common_of_221 {G : Type*} (D : Magma G)
    (hq : IsSideQuasigroup .right D) (h : @Equation221 G D) : Common D := by
  intro x y
  apply (hq x).1
  exact (h x y).symm.trans (h x x)

theorem core_unit {G : Type*} (D : Magma G) (h : @Equation221 G D) (x : G) :
    D.op (core D x) x = x := (h x x).symm

theorem core_core {G : Type*} (D : Magma G)
    (hq : IsSideQuasigroup .right D) (h : @Equation221 G D) (x : G) :
    core D (core D x) = D.op x x := by
  have he := common_of_221 D hq h (core D x) x
  rw [core_unit D h] at he
  exact he.symm

/-- Source row surjectivity follows directly from E115. It suffices for
this translation; source row injectivity and finiteness are not needed. -/
theorem translated {G : Type*} (M D : Magma G)
    (hd : IsDivision .right M D) (h : @Equation115 G M) (x a : G) :
    D.op a (D.op x a) = M.op x x := by
  let y := M.op (M.op a a) (M.op x x)
  have ha : M.op (M.op x x) y = a := (h a (M.op x x)).symm
  have hx : M.op y a = x := by simpa only [ha] using (h x y).symm
  have hda : D.op a y = M.op x x := by rw [← ha, hd.2]
  have hdx : D.op x a = y := by rw [← hx, hd.2]
  rw [hdx, hda]

theorem core_eq_square {G : Type*} (M D : Magma G)
    (hd : IsDivision .right M D) (h : @Equation115 G M) (x : G) :
    core D x = M.op x x := translated M D hd h x x

theorem forward {G : Type*} (M D : Magma G)
    (hd : IsDivision .right M D) (h : @Equation115 G M) : @Equation221 G D := by
  intro x y
  rw [translated M D hd h, hd.2]

theorem backward {G : Type*} (M D : Magma G)
    (hd : IsDivision .right M D) (h : @Equation221 G D) : @Equation115 G M := by
  have hq := sideQuasigroup_of_division (division_symm hd)
  have hc := common_of_221 D hq h
  have hs (x : G) : M.op x x = core D x := by
    have he := congrArg (fun z => M.op z x) (core_unit D h x)
    simpa only [hd.1] using he.symm
  intro x y
  rw [hs]
  let a := M.op (core D x) y
  have he : D.op x a = y := by
    apply left_injective D hq hc a
    exact (hc x a).trans (hd.2 (core D x) y).symm
  have hh := congrArg (fun z => M.op z a) he
  simpa only [hd.1] using hh

theorem characterizes_rightQuasigroups {G : Type} (D : Magma G)
    (hq : IsSideQuasigroup .right D) :
    @Equation221 G D ↔ InImage Law115 .right D := by
  constructor
  · intro h
    classical
    let e (y : G) := Equiv.ofBijective (fun x => D.op x y) (hq y)
    let M : Magma G := ⟨fun x y => (e y).symm x⟩
    have hd : IsDivision .right M D :=
      ⟨fun x y => (e y).symm_apply_apply x, fun x y => (e y).apply_symm_apply x⟩
    exact ⟨M, (@Law115.models_iff G M).mpr (backward M D hd h), hd⟩
  · rintro ⟨M, hm, hd⟩
    exact forward M D hd ((@Law115.models_iff G M).mp hm)

theorem image_core_bijective_fin {G : Type} [Finite G] (D : Magma G)
    (hi : InImage Law115 .right D) : Function.Bijective (core D) := by
  obtain ⟨M, hm, hd⟩ := hi
  have hq := sideQuasigroup_of_division (division_symm hd)
  have hc := common_of_221 D hq (forward M D hd ((@Law115.models_iff G M).mp hm))
  exact ⟨core_injective D hq hc, Finite.surjective_of_injective (core_injective D hq hc)⟩

/-- Multiplication recovery is exactly inversion of the recovered square.
This does not assert that the inverse is a uniform term in D. -/
theorem recovery_equation {G : Type*} (M D : Magma G)
    (hd : IsDivision .right M D) (h : @Equation115 G M) (x y : G) :
    core D (M.op x y) = D.op y x := by
  have hc : Common D := fun x y =>
    (translated M D hd h x y).trans (core_eq_square M D hd h x).symm
  have he := hc (M.op x y) y
  rw [hd.2] at he
  exact he.symm

@[implicit_reducible] def booleanCounterexample : Magma Bool := ⟨fun x y => !x && y⟩

theorem booleanCounterexample_221 : @Equation221 Bool booleanCounterexample := by decide

theorem booleanCounterexample_common : Common booleanCounterexample := by
  unfold Common core booleanCounterexample
  decide

theorem booleanCounterexample_not_image : ¬ InImage Law115 .right booleanCounterexample := by
  rintro ⟨M, _, hd⟩
  have hq := sideQuasigroup_of_division (division_symm hd)
  have he : false = true := (hq false).1 rfl
  exact Bool.noConfusion he

end Parastrophes.Eq115RightImage
