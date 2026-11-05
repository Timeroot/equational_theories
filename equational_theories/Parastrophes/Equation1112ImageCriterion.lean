import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All

/-!
# An exact division-only criterion for E1112

Among left quasigroups, the left-division image of E1112 is exactly the
class satisfying

    x*(y*z)=y  implies  z*(y*x)=x.

The hypothesis identifies z as the original product y*(x*y); the conclusion
then translates E1112 by cancelling two rows. This removes the original
multiplication from a model-search specification, without guessing a term
for its square map or its inverse. Both directions hold on arbitrary carriers.

This is a quasiidentity plus bijectivity, not an ordinary single identity.
It therefore does not settle a single-equation catalogue field.
-/
namespace Parastrophes.Eq1112Image
open Law

def Rotation {G : Type} (D : Magma G) : Prop :=
  ∀ x y z, D.op x (D.op y z) = y → D.op z (D.op y x) = x

theorem forward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation1112 G M) : Rotation D := by
  intro x y z hz
  have hs : D.op y z = M.op x y := by
    have he := congrArg (M.op x) hz
    simpa only [hd.1] using he
  have ht : z = M.op y (M.op x y) := by
    have he := congrArg (M.op y) hs
    simpa only [hd.1] using he
  have he := congrArg (D.op y) (h x y)
  rw [hd.2] at he
  rw [he, ← ht, hd.2]

theorem backward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : Rotation D) : @Equation1112 G M := by
  intro x y
  have he := h x y (M.op y (M.op x y)) (by rw [hd.2, hd.2])
  have ht := congrArg (M.op (M.op y (M.op x y))) he
  rw [hd.1] at ht
  have hh := congrArg (M.op y) ht
  simpa only [hd.1] using hh

theorem characterizes {G : Type} (D : Magma G) :
    InImage Law1112 .left D ↔ IsSideQuasigroup .left D ∧ Rotation D := by
  constructor
  · rintro ⟨M, hM, hd⟩
    exact ⟨sideQuasigroup_of_division (division_symm hd),
      forward M D hd ((@Law1112.models_iff G M).mp hM)⟩
  · rintro ⟨hq, hr⟩
    classical
    let e (x : G) := Equiv.ofBijective (D.op x) (hq x)
    let M : Magma G := ⟨fun x y => (e x).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (e x).symm_apply_apply y, fun x y => (e x).apply_symm_apply y⟩
    exact ⟨M, (@Law1112.models_iff G M).mpr (backward M D hd hr), hd⟩
end Parastrophes.Eq1112Image
