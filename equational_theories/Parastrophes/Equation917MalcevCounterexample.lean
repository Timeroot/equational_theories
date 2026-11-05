import equational_theories.Parastrophes.Equation917SandwichCandidate
import Mathlib.Data.Fin.VecNotation

/-!
# A Mal'cev-term test does not characterize E917's division image

Put q(x)=(x*(x*x))*x, U(x)=x*q(x), H(x,y)=q(x)*(x*y), and
R(x,w)=H(H(w,q(x)),x). In every actual division image, R is right division,
and p(x,y,z,w)=R(x,w)*H(U(z),R(y,w)) is a Mal'cev operation (for each w).
The converse is false: the two Mal'cev identities hold in the quasigroup below,
but U(0)=2. Thus they cannot replace the two defining image identities.

The table comes from F8=F2[b]/(b^3+b+1), with x*y=b^3*x+b*y+1.
Elements are encoded by the three binary coefficients. We verify the table
and terms directly in the kernel; no trust in the finite-field calculation or
external solver is required. This refutes one proposed compression only.
-/
namespace Parastrophes.Eq917Image.MalcevCounterexample
open SandwichCandidate (U H)

variable {A : Type} (D : Magma A)

def R (x w : A) := H D (H D w (core D x)) x

def p (x y z w : A) := D.op (R D x w) (H D (U D z) (R D y w))

/-- The two identities being tested really are consequences of image membership.
The argument works on arbitrary carriers. -/
theorem of_image (h : InImage Law917 .left D) :
    (∀ x y w, p D x x y w = y) ∧ (∀ x y w, p D x y y w = x) := by
  obtain ⟨M, hm, hd⟩ := h
  have hb := forward M D hd ((@Law917.models_iff A M).mp hm)
  have rows := sideQuasigroup_of_division (division_symm hd)
  have left (x y) : D.op x (H D y x) = y := (hb.2 y x).symm
  have unit (x) : U D x = x := (hb.1 x).symm
  have right (x w) : D.op (R D x w) w = x := by
    have he := left (R D x w) x
    have hh : H D x (R D x w) = w := by
      unfold H R
      rw [left, left]
    rwa [hh] at he
  constructor
  · intro x y w
    simp only [p, unit, left]
  · intro x y w
    have hh : H D y (R D y w) = w :=
      (rows (R D y w)).1 ((left _ _).trans (right y w).symm)
    simp only [p, unit, hh, right]

@[implicit_reducible] def bad : Magma (Fin 8) := ⟨fun x y =>
  (![![1, 3, 5, 7, 2, 0, 6, 4],
     ![2, 0, 6, 4, 1, 3, 5, 7],
     ![7, 5, 3, 1, 4, 6, 0, 2],
     ![4, 6, 0, 2, 7, 5, 3, 1],
     ![6, 4, 2, 0, 5, 7, 1, 3],
     ![5, 7, 1, 3, 6, 4, 2, 0],
     ![0, 2, 4, 6, 3, 1, 7, 5],
     ![3, 1, 7, 5, 0, 2, 4, 6]] :
    Fin 8 → Fin 8 → Fin 8) x y⟩

theorem bad_quasigroup : IsQuasigroup bad := by
  unfold IsQuasigroup Function.Bijective Function.Injective Function.Surjective
  decide +kernel

theorem bad_left_minor : ∀ x y w : Fin 8, p bad x x y w = y := by
  decide +kernel

theorem bad_right_minor : ∀ x y w : Fin 8, p bad x y y w = x := by
  decide +kernel

theorem bad_unit : U bad 0 = 2 := by decide +kernel

theorem bad_not_inImage : ¬ InImage Law917 .left bad := by
  intro h
  have hu := ((characterizes_fin bad).mpr h).1 0
  change (0 : Fin 8) = U bad 0 at hu
  rw [bad_unit] at hu
  exact (by decide : (0 : Fin 8) ≠ 2) hu

end Parastrophes.Eq917Image.MalcevCounterexample
