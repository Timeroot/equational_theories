import equational_theories.Parastrophes.Basic
import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation

/-!
# E477 in left-division notation

Among magmas with bijective rows, E477's left image is exactly E411 + E4332:
`x = x*(x*(x*(x*x)))` and `x*(y*x) = z*(y*z)`.

The row-bijectivity hypothesis is essential even on finite carriers: the
six-element counterexample below satisfies both equations but has row
collisions. This is not registered as an exact equational basis or a
single-equation characterization.

The crossed law makes the cubic map c(x)=x*(x*x) an endomorphism. The other
identity says x*(x*c(x))=x. Together they give a useful local right identity:
v(x)=x*c(x) satisfies x*v(x)=x and c(v(x))=v(x), without cancellation.
-/

namespace Parastrophes.Eq477Image
open Law

def core {A : Type} (D : Magma A) (x : A) := D.op x (D.op x x)

def Basis {A : Type} (D : Magma A) : Prop :=
  @Equation411 A D ∧ @Equation4332 A D

theorem cross {A : Type} (D : Magma A) (h : Basis D) (x y : A) :
    D.op x (D.op y x) = core D y := h.2 x y y

theorem diagonal {A : Type} (D : Magma A) (h : Basis D) (x : A) :
    D.op x (D.op x (core D x)) = x := (h.1 x).symm

theorem translated {A : Type} (M D : Magma A) (hd : IsDivision .left M D)
    (h : @Equation477 A M) (x y : A) :
    D.op x (D.op y x) = M.op y (M.op y y) := by
  have he := congrArg (D.op y) (h x y)
  rw [hd.2] at he
  exact (congrArg (D.op x) he).trans (hd.2 x (M.op y (M.op y y)))

theorem core_eq {A : Type} (M D : Magma A) (hd : IsDivision .left M D)
    (h : @Equation477 A M) (x : A) :
    core D x = M.op x (M.op x x) := translated M D hd h x x

theorem forward {A : Type} (M D : Magma A) (hd : IsDivision .left M D)
    (h : @Equation477 A M) : Basis D := by
  constructor
  · intro x
    change x = D.op x (D.op x (core D x))
    rw [core_eq M D hd h, hd.2, hd.2]
  · intro x y z
    rw [translated M D hd h, translated M D hd h]

theorem backward {A : Type} (M D : Magma A) (hd : IsDivision .left M D)
    (h : Basis D) : @Equation477 A M := by
  have hc (x : A) : M.op x (M.op x x) = core D x := by
    have he := congrArg (fun t => M.op x (M.op x t)) (h.1 x)
    change M.op x (M.op x x) = M.op x (M.op x (D.op x (D.op x (core D x)))) at he
    simpa only [hd.1] using he
  intro x y
  have he := congrArg (fun t => M.op y (M.op x t)) (cross D h x y)
  change M.op y (M.op x (D.op x (D.op y x))) = M.op y (M.op x (core D y)) at he
  rw [hd.1, hd.1, ← hc] at he
  exact he

/-- This is an exact characterization with the extra hypothesis retained. -/
theorem inImage_iff {A : Type} (D : Magma A) :
    InImage Law477 .left D ↔ Basis D ∧ IsSideQuasigroup .left D := by
  constructor
  · rintro ⟨M, hm, hd⟩
    exact ⟨forward M D hd ((@Law477.models_iff A M).mp hm),
      sideQuasigroup_of_division (division_symm hd)⟩
  · rintro ⟨hb, hq⟩
    classical
    let M : Magma A := ⟨fun x y => (Equiv.ofBijective (D.op x) (hq x)).symm y⟩
    have hd : IsDivision .left M D :=
      ⟨fun x y => (Equiv.ofBijective (D.op x) (hq x)).symm_apply_apply y,
       fun x y => (Equiv.ofBijective (D.op x) (hq x)).apply_symm_apply y⟩
    exact ⟨M, (@Law477.models_iff A M).mpr (backward M D hd hb), hd⟩

theorem rotate {A : Type} (D : Magma A) (h : Basis D) (x y : A) :
    D.op (D.op x y) (core D x) = core D y := by
  have he := cross D h (D.op x y) y
  rwa [cross D h y x] at he

theorem core_endomorphism {A : Type} (D : Magma A) (h : Basis D) (x y : A) :
    core D (D.op x y) = D.op (core D x) (core D y) := by
  have he := rotate D h y (D.op x y)
  rw [cross D h y x] at he
  exact he.symm

/-- Row cancellation forces the crossed cubic map to be injective, even on
an infinite carrier. If c(a)=c(b), crossing and cancellation first identify
the two rows. Applying those equal rows to their own indices and cancelling
twice then identifies a and b. Surjectivity is not used. -/
theorem core_injective_of_rows {A : Type} (D : Magma A) (h : Basis D)
    (hi : ∀ x, Function.Injective (D.op x)) : Function.Injective (core D) := by
  intro a b hab
  have rows (t : A) : D.op a t = D.op b t := by
    apply hi t
    rw [cross D h, cross D h, hab]
  apply hi a
  apply hi a
  calc
    D.op a (D.op a a) = core D b := hab
    _ = D.op a (D.op a b) := by
      change D.op b (D.op b b) = _
      rw [← rows b, ← rows (D.op a b)]

/-- The same hypotheses give cancellation in the other argument. -/
theorem columns_injective_of_rows {A : Type} (D : Magma A) (h : Basis D)
    (hi : ∀ x, Function.Injective (D.op x)) (y : A) :
    Function.Injective (fun x => D.op x y) := by
  intro a b hab
  apply core_injective_of_rows D h hi
  rw [← cross D h y a, ← cross D h y b]
  exact congrArg (D.op y) hab

/-- On finite carriers, the only missing condition in the two-equation basis
can equivalently be placed on its unary cubic map. This retains the condition;
the six-element counterexample below shows it cannot simply be omitted. -/
theorem inImage_iff_core_injective {A : Type} [Finite A] (D : Magma A) :
    InImage Law477 .left D ↔ Basis D ∧ Function.Injective (core D) := by
  constructor
  · intro hh
    obtain ⟨hb, hq⟩ := (inImage_iff D).mp hh
    exact ⟨hb, core_injective_of_rows D hb (fun x => (hq x).1)⟩
  · rintro ⟨hb, hi⟩
    have hs := Finite.surjective_of_injective hi
    apply (inImage_iff D).mpr
    refine ⟨hb, fun x => ?_⟩
    have onto : Function.Surjective (D.op x) := by
      intro y
      obtain ⟨z, rfl⟩ := hs y
      exact ⟨D.op z x, cross D hb x z⟩
    exact ⟨Finite.injective_iff_surjective.mpr onto, onto⟩

/-- Every element has a right identity fixed by the cubic endomorphism.
No row or column cancellation is used. -/
theorem local_right_identity {A : Type} (D : Magma A) (h : Basis D) (x : A) :
    D.op x (D.op x (core D x)) = x ∧
      core D (D.op x (core D x)) = D.op x (core D x) := by
  refine ⟨diagonal D h x, ?_⟩
  have he := rotate D h x (D.op x (core D x))
  rw [diagonal D h x] at he
  exact he.symm

/-- Surjective rows force the cubic map onto without any finite-carrier
argument. Choose the local unit v=x*c(x), fixed by c, and solve v*y=x.
Crossing twice gives y*x=v and c(y)=x*v=x. -/
theorem core_surjective_of_rows {A : Type} (D : Magma A) (h : Basis D)
    (hs : ∀ x, Function.Surjective (D.op x)) : Function.Surjective (core D) := by
  intro x
  let v := D.op x (core D x)
  obtain ⟨hv, hcv⟩ := local_right_identity D h x
  obtain ⟨y, hy⟩ := hs v x
  have hyx : D.op y x = v := by
    rw [← hy, cross D h y v]
    exact hcv
  exact ⟨y, by rw [← cross D h x y, hyx]; exact hv⟩

/-- A left-division image of E477 is actually a two-sided quasigroup, even
on an arbitrary carrier. This is conditional on the source admitting left
division; it does not assert that every E477 magma has division. -/
theorem image_quasigroup {A : Type} (D : Magma A)
    (h : InImage Law477 .left D) : IsQuasigroup D := by
  obtain ⟨hb, hq⟩ := (inImage_iff D).mp h
  have hs := core_surjective_of_rows D hb (fun x => (hq x).2)
  refine ⟨hq, fun y => ⟨columns_injective_of_rows D hb (fun x => (hq x).1) y, ?_⟩⟩
  intro z
  obtain ⟨a, ha⟩ := hs y
  obtain ⟨b, hb'⟩ := hs z
  refine ⟨D.op a b, ?_⟩
  change D.op (D.op a b) y = z
  rw [← ha, rotate D hb, hb']

/-- Mace4 found this counterexample to dropping row bijectivity. The checks
below are ordinary kernel-checked finite decisions, independent of Mace4. -/
@[implicit_reducible] def bad : Magma (Fin 6) := ⟨fun x y =>
  (![![2, 3, 0, 0, 4, 4],
     ![2, 3, 1, 0, 4, 4],
     ![0, 0, 4, 5, 2, 2],
     ![0, 0, 4, 5, 3, 2],
     ![4, 4, 2, 2, 0, 1],
     ![5, 4, 2, 2, 0, 1]] : Fin 6 → Fin 6 → Fin 6) x y⟩

theorem bad_basis : Basis bad := by
  unfold Basis
  decide

theorem bad_core : ∀ x : Fin 6, core bad x = ![0,0,2,2,4,4] x := by decide

theorem bad_not_inImage : ¬ InImage Law477 .left bad := by
  intro h
  have he := ((inImage_iff bad).mp h).2 0 |>.1
    (show bad.op 0 2 = bad.op 0 3 from rfl)
  exact (by decide : (2 : Fin 6) ≠ 3) he

/-- The two identities alone do not characterize the finite image. -/
theorem pair_not_sufficient :
    ¬ (∀ (A : Type) [Finite A] (D : Magma A), Basis D → InImage Law477 .left D) := by
  intro h
  exact bad_not_inImage (h (Fin 6) bad bad_basis)

end Parastrophes.Eq477Image
