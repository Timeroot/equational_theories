import equational_theories.Parastrophes.AffineIdentityCertificate
import equational_theories.Parastrophes.Equation872ImageBasis
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Constant-offset counterexamples to 144 proposed E872 image identities

All the operations have the form `D(x,y) = (1-i)*x + i*y + 1`, where `i² = -1`.
The proposed terms have variable coefficients `(1,0,0)` over the Gaussian integers.
Their constant coefficients vanish in the chosen finite rings, whereas the
necessary image identity `x = D(x, core(D,x))` has nonzero constant `2*i-1`.
The two nonsplit examples use `F₃[i]` and `F₇[i]`, with 9 and 49 elements.

The research indices below refer to the bounded rewrite search, NOT canonical
equation numbers. Every refutation is kernel checked using four coefficients,
without enumerating assignments. All the counterexamples are quasigroups.
-/
namespace Parastrophes.Eq872AffineOffsets
open Law FreeMagma AffineIdentityCertificate

private theorem not_image_of_unit_failure {R : Type} [CommRing R] (p q s : R)
    (h : (0 : R) ≠ (affine p q s).op 0 (Eq872Image.core (affine p q s) 0)) :
    ¬ InImage Law872 .left (affine p q s) := by
  rintro ⟨M, hM, hd⟩
  exact h ((Eq872Image.forward M _ hd ((@Law872.models_iff _ M).mp hM)).1 0)

private theorem refutes_fin {R : Type} [Finite R] (D : Magma R)
    (t : FreeMagma (Fin 3)) (ht : @satisfies _ R D (identity t))
    (hD : ¬ InImage Law872 .left D) :
    ¬ Characterizes .fin Law872 .left (identity t) := by
  intro h
  exact hD ((h R D (inferInstance : Finite R)).mp ht)

@[implicit_reducible] def prime13i5 : Magma (ZMod 13) := affine 9 5 1

def prime13i5Terms : List (FreeMagma (Fin 3)) := [
  -- 3673
  (Lf 1 ⋆ ((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ ((((Lf 0 ⋆ Lf 2) ⋆ (((Lf 0 ⋆ Lf 2) ⋆ (Lf 0 ⋆ Lf 2)) ⋆ (Lf 0 ⋆ Lf 2))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 2))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 3674
  (Lf 1 ⋆ ((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ ((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 4397
  (Lf 2 ⋆ ((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ ((((Lf 0 ⋆ Lf 1) ⋆ (((Lf 0 ⋆ Lf 1) ⋆ (Lf 0 ⋆ Lf 1)) ⋆ (Lf 0 ⋆ Lf 1))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 4400
  (Lf 2 ⋆ ((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ ((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 7230
  (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ ((Lf 0 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 8972
  (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ ((Lf 0 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10619
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ ((Lf 0 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 0 ⋆ Lf 2))) ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10621
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 2 ⋆ Lf 2))) ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10887
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ ((Lf 0 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 0 ⋆ Lf 1))) ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10888
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 1 ⋆ Lf 1))) ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 24245
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24271
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ ((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24464
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 24491
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ ((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 35699
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36628
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 53264
  (Lf 1 ⋆ ((((Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 53900
  (Lf 2 ⋆ ((((Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))))))) ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime13i5_coefficients : ∀ t ∈ prime13i5Terms,
    coefficients (R := ZMod 13) 9 5 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime13i5_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime13i5Terms) :
    @satisfies _ (ZMod 13) prime13i5 (identity t) :=
  satisfies_of_coefficients 9 5 1 t (prime13i5_coefficients t ht)

theorem prime13i5_not_image : ¬ InImage Law872 .left prime13i5 :=
  not_image_of_unit_failure 9 5 1 (by decide)

theorem prime13i5_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime13i5Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime13i5 t (prime13i5_satisfies t ht) prime13i5_not_image

theorem prime13i5_quasigroup : IsQuasigroup prime13i5 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨3, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨8, by decide⟩)

@[implicit_reducible] def prime37i6 : Magma (ZMod 37) := affine 32 6 1

def prime37i6Terms : List (FreeMagma (Fin 3)) := [
  -- 3764
  (Lf 1 ⋆ (((((Lf 0 ⋆ Lf 2) ⋆ (((Lf 0 ⋆ Lf 2) ⋆ (Lf 0 ⋆ Lf 2)) ⋆ (Lf 0 ⋆ Lf 2))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 2))) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 3796
  (Lf 1 ⋆ (((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 4527
  (Lf 2 ⋆ (((((Lf 0 ⋆ Lf 1) ⋆ (((Lf 0 ⋆ Lf 1) ⋆ (Lf 0 ⋆ Lf 1)) ⋆ (Lf 0 ⋆ Lf 1))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 4577
  (Lf 2 ⋆ (((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10643
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10645
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10911
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10912
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 14428
  (Lf 1 ⋆ ((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 14429
  (Lf 1 ⋆ ((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 15093
  (Lf 2 ⋆ ((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 15094
  (Lf 2 ⋆ ((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24261
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24482
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 33290
  (((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 33313
  (((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime37i6_coefficients : ∀ t ∈ prime37i6Terms,
    coefficients (R := ZMod 37) 32 6 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime37i6_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime37i6Terms) :
    @satisfies _ (ZMod 37) prime37i6 (identity t) :=
  satisfies_of_coefficients 32 6 1 t (prime37i6_coefficients t ht)

theorem prime37i6_not_image : ¬ InImage Law872 .left prime37i6 :=
  not_image_of_unit_failure 32 6 1 (by decide)

theorem prime37i6_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime37i6Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime37i6 t (prime37i6_satisfies t ht) prime37i6_not_image

theorem prime37i6_quasigroup : IsQuasigroup prime37i6 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨22, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨31, by decide⟩)

@[implicit_reducible] def prime13i8 : Magma (ZMod 13) := affine 6 8 1

def prime13i8Terms : List (FreeMagma (Fin 3)) := [
  -- 6386
  ((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ ((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 6632
  ((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ ((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10616
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))))))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10884
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))))))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 16652
  (((Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 18151
  (((Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 35704
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ ((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36631
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ ((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime13i8_coefficients : ∀ t ∈ prime13i8Terms,
    coefficients (R := ZMod 13) 6 8 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime13i8_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime13i8Terms) :
    @satisfies _ (ZMod 13) prime13i8 (identity t) :=
  satisfies_of_coefficients 6 8 1 t (prime13i8_coefficients t ht)

theorem prime13i8_not_image : ¬ InImage Law872 .left prime13i8 :=
  not_image_of_unit_failure 6 8 1 (by decide)

theorem prime13i8_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime13i8Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime13i8 t (prime13i8_satisfies t ht) prime13i8_not_image

theorem prime13i8_quasigroup : IsQuasigroup prime13i8 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨11, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨5, by decide⟩)

abbrev Gaussian3 := QuadraticAlgebra (ZMod 3) (-1) 0

instance : Finite Gaussian3 :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm

@[implicit_reducible] def gaussian3 : Magma (Gaussian3) := affine ⟨1,-1⟩ ⟨0,1⟩ 1

def gaussian3Terms : List (FreeMagma (Fin 3)) := [
  -- 10622
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10624
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10890
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10891
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 14005
  (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 14679
  (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 15714
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 17264
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24273
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24495
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 39305
  (Lf 1 ⋆ ((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ ((Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 41041
  (Lf 2 ⋆ ((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ ((Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))))))) ⋆ (Lf 2 ⋆ Lf 0)))]

theorem gaussian3_coefficients : ∀ t ∈ gaussian3Terms,
    coefficients (R := Gaussian3) ⟨1,-1⟩ ⟨0,1⟩ 1 t = ⟨1,0,0,0⟩ := by decide

theorem gaussian3_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ gaussian3Terms) :
    @satisfies _ (Gaussian3) gaussian3 (identity t) :=
  satisfies_of_coefficients (R := Gaussian3) ⟨1,-1⟩ ⟨0,1⟩ 1 t (gaussian3_coefficients t ht)

theorem gaussian3_not_image : ¬ InImage Law872 .left gaussian3 :=
  not_image_of_unit_failure (R := Gaussian3) ⟨1,-1⟩ ⟨0,1⟩ 1 (by decide)

theorem gaussian3_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ gaussian3Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin gaussian3 t (gaussian3_satisfies t ht) gaussian3_not_image

theorem gaussian3_quasigroup : IsQuasigroup gaussian3 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨⟨2,2⟩, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨⟨0,-1⟩, by decide⟩)

abbrev Gaussian7 := QuadraticAlgebra (ZMod 7) (-1) 0

instance : Finite Gaussian7 :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd (-1 : ZMod 7) 0).symm

@[implicit_reducible] def gaussian7 : Magma (Gaussian7) := affine ⟨1,-1⟩ ⟨0,1⟩ 1

def gaussian7Terms : List (FreeMagma (Fin 3)) := [
  -- 10625
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 0 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 0 ⋆ Lf 2))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10627
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 2 ⋆ Lf 2))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10628
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10630
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10893
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 0 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 0 ⋆ Lf 1))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10894
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 1 ⋆ Lf 1))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10896
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10897
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 24282
  ((Lf 1 ⋆ (((Lf 2 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24505
  ((Lf 2 ⋆ (((Lf 1 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))]

theorem gaussian7_coefficients : ∀ t ∈ gaussian7Terms,
    coefficients (R := Gaussian7) ⟨1,-1⟩ ⟨0,1⟩ 1 t = ⟨1,0,0,0⟩ := by decide

theorem gaussian7_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ gaussian7Terms) :
    @satisfies _ (Gaussian7) gaussian7 (identity t) :=
  satisfies_of_coefficients (R := Gaussian7) ⟨1,-1⟩ ⟨0,1⟩ 1 t (gaussian7_coefficients t ht)

theorem gaussian7_not_image : ¬ InImage Law872 .left gaussian7 :=
  not_image_of_unit_failure (R := Gaussian7) ⟨1,-1⟩ ⟨0,1⟩ 1 (by decide)

theorem gaussian7_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ gaussian7Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin gaussian7 t (gaussian7_satisfies t ht) gaussian7_not_image

theorem gaussian7_quasigroup : IsQuasigroup gaussian7 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨⟨4,4⟩, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨⟨0,-1⟩, by decide⟩)

@[implicit_reducible] def prime109i76 : Magma (ZMod 109) := affine 34 76 1

def prime109i76Terms : List (FreeMagma (Fin 3)) := [
  -- 10631
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((((Lf 0 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 0 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10633
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((((Lf 2 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 2 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10899
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((((Lf 0 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 0 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10900
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((((Lf 1 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 1 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))]

theorem prime109i76_coefficients : ∀ t ∈ prime109i76Terms,
    coefficients (R := ZMod 109) 34 76 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime109i76_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime109i76Terms) :
    @satisfies _ (ZMod 109) prime109i76 (identity t) :=
  satisfies_of_coefficients 34 76 1 t (prime109i76_coefficients t ht)

theorem prime109i76_not_image : ¬ InImage Law872 .left prime109i76 :=
  not_image_of_unit_failure 34 76 1 (by decide)

theorem prime109i76_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime109i76Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime109i76 t (prime109i76_satisfies t ht) prime109i76_not_image

theorem prime109i76_quasigroup : IsQuasigroup prime109i76 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨93, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨33, by decide⟩)

@[implicit_reducible] def prime41i32 : Magma (ZMod 41) := affine 10 32 1

def prime41i32Terms : List (FreeMagma (Fin 3)) := [
  -- 10634
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10636
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10902
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10903
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 14433
  (Lf 1 ⋆ ((Lf 2 ⋆ ((((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 14434
  (Lf 1 ⋆ ((Lf 2 ⋆ ((((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 15098
  (Lf 2 ⋆ ((Lf 1 ⋆ ((((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 15099
  (Lf 2 ⋆ ((Lf 1 ⋆ ((((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24243
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ ((((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 2))) ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24461
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ ((((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 1))) ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))]

theorem prime41i32_coefficients : ∀ t ∈ prime41i32Terms,
    coefficients (R := ZMod 41) 10 32 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime41i32_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime41i32Terms) :
    @satisfies _ (ZMod 41) prime41i32 (identity t) :=
  satisfies_of_coefficients 10 32 1 t (prime41i32_coefficients t ht)

theorem prime41i32_not_image : ¬ InImage Law872 .left prime41i32 :=
  not_image_of_unit_failure 10 32 1 (by decide)

theorem prime41i32_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime41i32Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime41i32 t (prime41i32_satisfies t ht) prime41i32_not_image

theorem prime41i32_quasigroup : IsQuasigroup prime41i32 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨37, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨9, by decide⟩)

@[implicit_reducible] def prime41i9 : Magma (ZMod 41) := affine 33 9 1

def prime41i9Terms : List (FreeMagma (Fin 3)) := [
  -- 10637
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (((Lf 0 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 0 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10639
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (((Lf 2 ⋆ ((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 2 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10905
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (((Lf 0 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 0 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 10906
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (((Lf 1 ⋆ ((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 1 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 38435
  (Lf 1 ⋆ ((Lf 0 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 40239
  (Lf 2 ⋆ ((Lf 0 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime41i9_coefficients : ∀ t ∈ prime41i9Terms,
    coefficients (R := ZMod 41) 33 9 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime41i9_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime41i9Terms) :
    @satisfies _ (ZMod 41) prime41i9 (identity t) :=
  satisfies_of_coefficients 33 9 1 t (prime41i9_coefficients t ht)

theorem prime41i9_not_image : ¬ InImage Law872 .left prime41i9 :=
  not_image_of_unit_failure 33 9 1 (by decide)

theorem prime41i9_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime41i9Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime41i9 t (prime41i9_satisfies t ht) prime41i9_not_image

theorem prime41i9_quasigroup : IsQuasigroup prime41i9 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨5, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨32, by decide⟩)

@[implicit_reducible] def prime17i13 : Magma (ZMod 17) := affine 5 13 1

def prime17i13Terms : List (FreeMagma (Fin 3)) := [
  -- 10649
  ((Lf 1 ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 10917
  ((Lf 2 ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 16041
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 17568
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24265
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24267
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (((((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24488
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (((((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 24489
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 34297
  (Lf 1 ⋆ ((Lf 0 ⋆ (((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 34907
  (Lf 2 ⋆ ((Lf 0 ⋆ (((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))))))) ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime17i13_coefficients : ∀ t ∈ prime17i13Terms,
    coefficients (R := ZMod 17) 5 13 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime17i13_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime17i13Terms) :
    @satisfies _ (ZMod 17) prime17i13 (identity t) :=
  satisfies_of_coefficients 5 13 1 t (prime17i13_coefficients t ht)

theorem prime17i13_not_image : ¬ InImage Law872 .left prime17i13 :=
  not_image_of_unit_failure 5 13 1 (by decide)

theorem prime17i13_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime17i13Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime17i13 t (prime17i13_satisfies t ht) prime17i13_not_image

theorem prime17i13_quasigroup : IsQuasigroup prime17i13 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨7, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨4, by decide⟩)

@[implicit_reducible] def prime29i12 : Magma (ZMod 29) := affine 18 12 1

def prime29i12Terms : List (FreeMagma (Fin 3)) := [
  -- 16007
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ ((((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 16053
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 16268
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 17543
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ ((((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 17580
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 17786
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 34302
  (Lf 1 ⋆ ((Lf 0 ⋆ (((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 34419
  (Lf 1 ⋆ ((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ (((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 34912
  (Lf 2 ⋆ ((Lf 0 ⋆ (((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 35018
  (Lf 2 ⋆ ((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ (((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 35756
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36680
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime29i12_coefficients : ∀ t ∈ prime29i12Terms,
    coefficients (R := ZMod 29) 18 12 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime29i12_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime29i12Terms) :
    @satisfies _ (ZMod 29) prime29i12 (identity t) :=
  satisfies_of_coefficients 18 12 1 t (prime29i12_coefficients t ht)

theorem prime29i12_not_image : ¬ InImage Law872 .left prime29i12 :=
  not_image_of_unit_failure 18 12 1 (by decide)

theorem prime29i12_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime29i12Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime29i12 t (prime29i12_satisfies t ht) prime29i12_not_image

theorem prime29i12_quasigroup : IsQuasigroup prime29i12 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨21, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨17, by decide⟩)

@[implicit_reducible] def prime17i4 : Magma (ZMod 17) := affine 14 4 1

def prime17i4Terms : List (FreeMagma (Fin 3)) := [
  -- 16047
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 17574
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 18479
  ((((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 18800
  ((((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime17i4_coefficients : ∀ t ∈ prime17i4Terms,
    coefficients (R := ZMod 17) 14 4 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime17i4_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime17i4Terms) :
    @satisfies _ (ZMod 17) prime17i4 (identity t) :=
  satisfies_of_coefficients 14 4 1 t (prime17i4_coefficients t ht)

theorem prime17i4_not_image : ¬ InImage Law872 .left prime17i4 :=
  not_image_of_unit_failure 14 4 1 (by decide)

theorem prime17i4_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime17i4Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime17i4 t (prime17i4_satisfies t ht) prime17i4_not_image

theorem prime17i4_quasigroup : IsQuasigroup prime17i4 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨11, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨13, by decide⟩)

@[implicit_reducible] def prime89i55 : Magma (ZMod 89) := affine 35 55 1

def prime89i55Terms : List (FreeMagma (Fin 3)) := [
  -- 16059
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 17586
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 35854
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36772
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime89i55_coefficients : ∀ t ∈ prime89i55Terms,
    coefficients (R := ZMod 89) 35 55 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime89i55_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime89i55Terms) :
    @satisfies _ (ZMod 89) prime89i55 (identity t) :=
  satisfies_of_coefficients 35 55 1 t (prime89i55_coefficients t ht)

theorem prime89i55_not_image : ¬ InImage Law872 .left prime89i55 :=
  not_image_of_unit_failure 35 55 1 (by decide)

theorem prime89i55_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime89i55Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime89i55 t (prime89i55_satisfies t ht) prime89i55_not_image

theorem prime89i55_quasigroup : IsQuasigroup prime89i55 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨28, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨34, by decide⟩)

@[implicit_reducible] def prime53i23 : Magma (ZMod 53) := affine 31 23 1

def prime53i23Terms : List (FreeMagma (Fin 3)) := [
  -- 16065
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 17592
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 34303
  (Lf 1 ⋆ ((Lf 0 ⋆ (((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 34913
  (Lf 2 ⋆ ((Lf 0 ⋆ (((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)))) ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 35713
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ ((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36639
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ ((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime53i23_coefficients : ∀ t ∈ prime53i23Terms,
    coefficients (R := ZMod 53) 31 23 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime53i23_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime53i23Terms) :
    @satisfies _ (ZMod 53) prime53i23 (identity t) :=
  satisfies_of_coefficients 31 23 1 t (prime53i23_coefficients t ht)

theorem prime53i23_not_image : ¬ InImage Law872 .left prime53i23 :=
  not_image_of_unit_failure 31 23 1 (by decide)

theorem prime53i23_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime53i23Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime53i23 t (prime53i23_satisfies t ht) prime53i23_not_image

theorem prime53i23_quasigroup : IsQuasigroup prime53i23 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨12, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨30, by decide⟩)

@[implicit_reducible] def prime73i46 : Magma (ZMod 73) := affine 28 46 1

def prime73i46Terms : List (FreeMagma (Fin 3)) := [
  -- 24251
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 2))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24253
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24470
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 1))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 24473
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))]

theorem prime73i46_coefficients : ∀ t ∈ prime73i46Terms,
    coefficients (R := ZMod 73) 28 46 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime73i46_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime73i46Terms) :
    @satisfies _ (ZMod 73) prime73i46 (identity t) :=
  satisfies_of_coefficients 28 46 1 t (prime73i46_coefficients t ht)

theorem prime73i46_not_image : ¬ InImage Law872 .left prime73i46 :=
  not_image_of_unit_failure 28 46 1 (by decide)

theorem prime73i46_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime73i46Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime73i46 t (prime73i46_satisfies t ht) prime73i46_not_image

theorem prime73i46_quasigroup : IsQuasigroup prime73i46 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨60, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨27, by decide⟩)

@[implicit_reducible] def prime53i30 : Magma (ZMod 53) := affine 24 30 1

def prime53i30Terms : List (FreeMagma (Fin 3)) := [
  -- 24257
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24259
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((((((Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2)) ⋆ (Lf 2 ⋆ ((Lf 2 ⋆ Lf 2) ⋆ Lf 2))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 2))) ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24479
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((((((Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1)) ⋆ (Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 1))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 24480
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))]

theorem prime53i30_coefficients : ∀ t ∈ prime53i30Terms,
    coefficients (R := ZMod 53) 24 30 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime53i30_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime53i30Terms) :
    @satisfies _ (ZMod 53) prime53i30 (identity t) :=
  satisfies_of_coefficients 24 30 1 t (prime53i30_coefficients t ht)

theorem prime53i30_not_image : ¬ InImage Law872 .left prime53i30 :=
  not_image_of_unit_failure 24 30 1 (by decide)

theorem prime53i30_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime53i30Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime53i30 t (prime53i30_satisfies t ht) prime53i30_not_image

theorem prime53i30_quasigroup : IsQuasigroup prime53i30 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨42, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨23, by decide⟩)

@[implicit_reducible] def prime29i17 : Magma (ZMod 29) := affine 13 17 1

def prime29i17Terms : List (FreeMagma (Fin 3)) := [
  -- 25128
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (((Lf 0 ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 0 ⋆ ((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 28980
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (((Lf 0 ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 0 ⋆ ((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime29i17_coefficients : ∀ t ∈ prime29i17Terms,
    coefficients (R := ZMod 29) 13 17 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime29i17_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime29i17Terms) :
    @satisfies _ (ZMod 29) prime29i17 (identity t) :=
  satisfies_of_coefficients 13 17 1 t (prime29i17_coefficients t ht)

theorem prime29i17_not_image : ¬ InImage Law872 .left prime29i17 :=
  not_image_of_unit_failure 13 17 1 (by decide)

theorem prime29i17_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime29i17Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime29i17 t (prime29i17_satisfies t ht) prime29i17_not_image

theorem prime29i17_quasigroup : IsQuasigroup prime29i17 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨9, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨12, by decide⟩)

@[implicit_reducible] def prime37i31 : Magma (ZMod 37) := affine 7 31 1

def prime37i31Terms : List (FreeMagma (Fin 3)) := [
  -- 35717
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 35900
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36644
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 36816
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime37i31_coefficients : ∀ t ∈ prime37i31Terms,
    coefficients (R := ZMod 37) 7 31 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime37i31_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime37i31Terms) :
    @satisfies _ (ZMod 37) prime37i31 (identity t) :=
  satisfies_of_coefficients 7 31 1 t (prime37i31_coefficients t ht)

theorem prime37i31_not_image : ¬ InImage Law872 .left prime37i31 :=
  not_image_of_unit_failure 7 31 1 (by decide)

theorem prime37i31_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime37i31Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime37i31 t (prime37i31_satisfies t ht) prime37i31_not_image

theorem prime37i31_quasigroup : IsQuasigroup prime37i31 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨16, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨6, by decide⟩)

@[implicit_reducible] def prime97i75 : Magma (ZMod 97) := affine 23 75 1

def prime97i75Terms : List (FreeMagma (Fin 3)) := [
  -- 35722
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((((Lf 2 ⋆ Lf 1) ⋆ (((Lf 2 ⋆ Lf 1) ⋆ (Lf 2 ⋆ Lf 1)) ⋆ (Lf 2 ⋆ Lf 1))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 1))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 35726
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36647
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((((Lf 1 ⋆ Lf 2) ⋆ (((Lf 1 ⋆ Lf 2) ⋆ (Lf 1 ⋆ Lf 2)) ⋆ (Lf 1 ⋆ Lf 2))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 2))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 36652
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime97i75_coefficients : ∀ t ∈ prime97i75Terms,
    coefficients (R := ZMod 97) 23 75 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime97i75_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime97i75Terms) :
    @satisfies _ (ZMod 97) prime97i75 (identity t) :=
  satisfies_of_coefficients 23 75 1 t (prime97i75_coefficients t ht)

theorem prime97i75_not_image : ¬ InImage Law872 .left prime97i75 :=
  not_image_of_unit_failure 23 75 1 (by decide)

theorem prime97i75_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime97i75Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime97i75 t (prime97i75_satisfies t ht) prime97i75_not_image

theorem prime97i75_quasigroup : IsQuasigroup prime97i75 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨38, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨22, by decide⟩)

@[implicit_reducible] def prime101i10 : Magma (ZMod 101) := affine 92 10 1

def prime101i10Terms : List (FreeMagma (Fin 3)) := [
  -- 38439
  (Lf 1 ⋆ ((Lf 0 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))))))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 40243
  (Lf 2 ⋆ ((Lf 0 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))))))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime101i10_coefficients : ∀ t ∈ prime101i10Terms,
    coefficients (R := ZMod 101) 92 10 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime101i10_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime101i10Terms) :
    @satisfies _ (ZMod 101) prime101i10 (identity t) :=
  satisfies_of_coefficients 92 10 1 t (prime101i10_coefficients t ht)

theorem prime101i10_not_image : ¬ InImage Law872 .left prime101i10 :=
  not_image_of_unit_failure 92 10 1 (by decide)

theorem prime101i10_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime101i10Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime101i10 t (prime101i10_satisfies t ht) prime101i10_not_image

theorem prime101i10_quasigroup : IsQuasigroup prime101i10 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨56, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨91, by decide⟩)

@[implicit_reducible] def prime97i22 : Magma (ZMod 97) := affine 76 22 1

def prime97i22Terms : List (FreeMagma (Fin 3)) := [
  -- 56441
  (Lf 1 ⋆ ((Lf 0 ⋆ ((((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 56442
  (Lf 1 ⋆ ((Lf 0 ⋆ ((((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 2 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))),
  -- 57854
  (Lf 2 ⋆ ((Lf 0 ⋆ ((((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (((Lf 0 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))),
  -- 57855
  (Lf 2 ⋆ ((Lf 0 ⋆ ((((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (((Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ ((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)))) ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0)))]

theorem prime97i22_coefficients : ∀ t ∈ prime97i22Terms,
    coefficients (R := ZMod 97) 76 22 1 t = ⟨1,0,0,0⟩ := by decide

theorem prime97i22_satisfies (t : FreeMagma (Fin 3)) (ht : t ∈ prime97i22Terms) :
    @satisfies _ (ZMod 97) prime97i22 (identity t) :=
  satisfies_of_coefficients 76 22 1 t (prime97i22_coefficients t ht)

theorem prime97i22_not_image : ¬ InImage Law872 .left prime97i22 :=
  not_image_of_unit_failure 76 22 1 (by decide)

theorem prime97i22_refutes (t : FreeMagma (Fin 3)) (ht : t ∈ prime97i22Terms) :
    ¬ Characterizes .fin Law872 .left (identity t) :=
  refutes_fin prime97i22 t (prime97i22_satisfies t ht) prime97i22_not_image

theorem prime97i22_quasigroup : IsQuasigroup prime97i22 :=
  quasigroup_fin _ _ _ (isUnit_iff_exists_inv.mpr ⟨60, by decide⟩)
    (isUnit_iff_exists_inv.mpr ⟨75, by decide⟩)

end Parastrophes.Eq872AffineOffsets
