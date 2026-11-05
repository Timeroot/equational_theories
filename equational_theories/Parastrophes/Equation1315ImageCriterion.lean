import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All

/-!
# E1315 in division notation

A left quasigroup belongs to E1315's left-division image exactly when it
satisfies the seven-operation equation E13834319:

    (a*b)*a = b*((a*b)*((a*b)*a)).

To see the rotation, set y=a*b and x=y*a in division notation. In the
original multiplication, y*x=a and a*y=b. E1315 is then x=y*(b*x).
Two divisions give the displayed identity. Reversing the substitutions
proves the converse. Neither direction uses finiteness.

The left-quasigroup hypothesis is essential: every constant magma satisfies
the displayed identity. This is an exact conditional characterization,
not an unrestricted single-equation result or catalogue row closure.
-/
namespace Parastrophes.Eq1315Image
open Law FreeMagma

def Rotation {G : Type} (D : Magma G) : Prop :=
  ∀ a b, D.op (D.op a b) a =
    D.op b (D.op (D.op a b) (D.op (D.op a b) a))

/-- Eliminate multiplication by using two adjacent products as new variables. -/
theorem forward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : @Equation1315 G M) : Rotation D := by
  intro a b
  let y := D.op a b
  let x := D.op y a
  have he := h x y
  change x = M.op y (M.op (M.op (M.op y x) y) x) at he
  have hyx : M.op y x = a := hd.1 y a
  have hay : M.op a y = b := hd.1 a b
  rw [hyx, hay] at he
  have hh := congrArg (D.op y) he
  rw [hd.2] at hh
  have hh' := congrArg (D.op b) hh
  rw [hd.2] at hh'
  exact hh'.symm

/-- Specialize the two variables to those original products. -/
theorem backward {G : Type} (M D : Magma G) (hd : IsDivision .left M D)
    (h : Rotation D) : @Equation1315 G M := by
  intro x y
  have he := h (M.op y x) (M.op (M.op y x) y)
  rw [hd.2, hd.2] at he
  have hh := congrArg (M.op (M.op (M.op y x) y)) he
  rw [hd.1] at hh
  have hh' := congrArg (M.op y) hh
  rw [hd.1] at hh'
  exact hh'.symm

theorem characterizes {G : Type} (D : Magma G) :
    InImage Law1315 .left D ↔ IsSideQuasigroup .left D ∧ Rotation D := by
  constructor
  · rintro ⟨M, hm, hd⟩
    exact ⟨sideQuasigroup_of_division (division_symm hd),
      forward M D hd ((@Law1315.models_iff G M).mp hm)⟩
  · rintro ⟨hq, hr⟩
    classical
    let e (x : G) := Equiv.ofBijective (D.op x) (hq x)
    let M : Magma G := ⟨fun x y => (e x).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (e x).symm_apply_apply y, fun x y => (e x).apply_symm_apply y⟩
    exact ⟨M, (@Law1315.models_iff G M).mpr (backward M D hd hr), hd⟩
/-- The canonical extended number is E13834319 (seven operations). -/
def rotationLaw : NatMagmaLaw :=
  let a := Lf 0
  let b := Lf 1
  let t := a ⋆ b
  let u := t ⋆ a
  ⟨u, b ⋆ (t ⋆ u)⟩

theorem rotationLaw_iff {G : Type} (D : Magma G) :
    @satisfies _ G D rotationLaw ↔ Rotation D := by
  constructor
  · intro h a b
    exact h (fun n => if n = 0 then a else b)
  · intro h v
    exact h (v 0) (v 1)

/-- The equation alone cannot replace the explicit bijectivity requirement. -/
theorem rotation_not_sufficient :
    ∃ D : Magma Bool, Rotation D ∧ ¬ InImage Law1315 .left D := by
  let D : Magma Bool := ⟨fun _ _ => false⟩
  refine ⟨D, fun _ _ => rfl, ?_⟩
  intro hi
  have hq := ((characterizes D).mp hi).1 false
  exact Bool.false_ne_true (hq.1 (show D.op false false = D.op false true from rfl))

end Parastrophes.Eq1315Image
