import equational_theories.Parastrophes.AffineIdentityCertificate
import equational_theories.Parastrophes.Equation872ImageBasis
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# The Gaussian affine family and two E872 image candidates

For `D(x,y)=(1-i)*x+i*y+1`, with `i*i=-1`, the exact E872 left-image
criterion is `2*i=1`. This works over any commutative ring, with no finiteness
assumption: every row has an explicit inverse.

Four candidates surviving the Gaussian counterexamples form two pairs under
variable renaming. The cubic counterexample module subsequently refutes the
28-operation pair outside this family. Their Gaussian-integer coefficients are checked once and
transported by a ring homomorphism. Each pair characterizes the image WITHIN
THIS FAMILY. The unrestricted single-equation question remains open.
-/
namespace Parastrophes.Eq872GaussianAffine
open Law AffineIdentityCertificate
variable {R : Type} [CommRing R] (i : R) (hi : i * i = -1)

@[implicit_reducible] def magma : Magma R := affine (1-i) i 1

@[simp] theorem magma_op (x y : R) : (magma i).op x y = (1-i)*x+i*y+1 := rfl

include hi

theorem core_value (x : R) : Eq872Image.core (magma i) x = x+2+2*i := by
  dsimp [Eq872Image.core, magma, affine]
  linear_combination -hi

theorem unit_value (x : R) : (magma i).op x (Eq872Image.core (magma i) x) =
    x+(2*i-1) := by
  rw [core_value i hi]
  simp only [magma_op]
  linear_combination 2*hi

theorem cross_value (x y : R) :
    (magma i).op y ((magma i).op (Eq872Image.core (magma i) x) ((magma i).op y x)) =
    x+5*i := by
  rw [core_value i hi]
  simp only [magma_op]
  linear_combination (i*x-i*y-2*i-x+y+1)*hi

theorem basis_iff : Eq872Image.Basis (magma i) ↔ 2*i=1 := by
  constructor
  · intro h
    have he := h.1 0
    change 0 = (magma i).op 0 (Eq872Image.core (magma i) 0) at he
    rw [unit_value i hi, zero_add] at he
    exact sub_eq_zero.mp he.symm
  · intro h
    have hc : (5:R)*i=0 := by
      linear_combination (2-i)*(h : 2*i=1) + 2*hi
    constructor
    · intro x
      change x = (magma i).op x (Eq872Image.core (magma i) x)
      rw [unit_value i hi, h]
      simp
    · intro x y
      rw [cross_value i hi, hc, add_zero]

/-- Every row is invertible without finiteness: its linear coefficient is i. -/
theorem left_division : IsDivision .left (magma i)
    (⟨fun x y => -i*(y-(1-i)*x-1)⟩ : Magma R) := by
  constructor
  · intro x y
    change (1-i)*x+i*(-i*(y-(1-i)*x-1))+1=y
    linear_combination -(i*x-x+y-1)*hi
  · intro x y
    change -i*((1-i)*x+i*y+1-(1-i)*x-1)=y
    linear_combination -y*hi

/-- The criterion is exact on arbitrary coefficient rings, not only finite ones. -/
theorem image_iff : InImage Law872 .left (magma i) ↔ 2*i=1 := by
  constructor
  · rintro ⟨M, hM, hd⟩
    exact (basis_iff i hi).mp (Eq872Image.forward M _ hd ((@Law872.models_iff R M).mp hM))
  · intro h
    let M : Magma R := ⟨fun x y => -i*(y-(1-i)*x-1)⟩
    have hd : IsDivision .left M (magma i) := division_symm (left_division i hi)
    exact ⟨M, (@Law872.models_iff R M).mpr
      (Eq872Image.backward M _ hd ((basis_iff i hi).mpr h)), hd⟩

abbrev GaussianZ := QuadraticAlgebra ℤ (-1) 0

def specialize : GaussianZ →+* R :=
  (QuadraticAlgebra.lift (R := ℤ) (a := -1) (b := 0)
    ⟨i, by simpa using hi⟩ : GaussianZ →ₐ[ℤ] R).toRingHom

@[simp] theorem specialize_mk (a b : ℤ) :
    specialize i hi ⟨a,b⟩ = (a : R)+(b : R)*i := by
  simp [specialize, QuadraticAlgebra.lift, zsmul_eq_mul]

/-- Exact Gaussian-integer coefficients specialize to any commutative ring
with a chosen square root of -1, including nonfields and rings with nilpotents. -/
theorem eval_of_gaussian_coefficients (t : FreeMagma (Fin 3)) (a b : ℤ)
    (h : coefficients (R := GaussianZ) ⟨1,-1⟩ ⟨0,1⟩ 1 t = ⟨1,0,0,⟨a,b⟩⟩)
    (v : Fin 3 → R) :
    @FreeMagma.evalInMagma _ R (magma i) v t = v 0 + (a : R)+(b : R)*i := by
  have hc := coefficients_map (specialize i hi) (⟨1,-1⟩ : GaussianZ) ⟨0,1⟩ 1 t
  rw [h] at hc
  have hp : specialize i hi (⟨1,-1⟩ : GaussianZ) = 1-i := by simp [sub_eq_add_neg]
  have hq : specialize i hi (⟨0,1⟩ : GaussianZ) = i := by simp
  rw [hp, hq, map_one] at hc
  have he := eval_eq_value (1-i) i 1 t v
  rw [hc] at he
  simpa [Coefficients.map, value, add_assoc] using he


theorem identity_iff_constant (t : FreeMagma (Fin 3)) (a b : ℤ)
    (h : coefficients (R := GaussianZ) ⟨1,-1⟩ ⟨0,1⟩ 1 t = ⟨1,0,0,⟨a,b⟩⟩) :
    @satisfies _ R (magma i) (identity t) ↔ (a : R)+(b : R)*i=0 := by
  letI : Magma R := magma i
  have he (v : ℕ → R) :
      FreeMagma.evalInMagma v (FreeMagma.fmapFreeMagma Fin.val t) =
      v 0+(a : R)+(b : R)*i := by
    rw [← FreeMagma.evalInMagma_comp]
    exact eval_of_gaussian_coefficients i hi t a b h (v ∘ Fin.val)
  constructor
  · intro ht
    have hz := ht (fun _ => 0)
    change 0 = FreeMagma.evalInMagma (fun _ => 0) (FreeMagma.fmapFreeMagma Fin.val t) at hz
    rw [he] at hz
    simpa using hz.symm
  · intro hc v
    change v 0 = FreeMagma.evalInMagma v (FreeMagma.fmapFreeMagma Fin.val t)
    rw [he]
    linear_combination -hc

omit hi
open FreeMagma

/-- The surviving 26-operation pair differs only by swapping y and z. -/
def candidates26 : List (FreeMagma (Fin 3)) := [
  -- 24237
  ((Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))))))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0))),
  -- 24455
  ((Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (((Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) ⋆ (Lf 0 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0))) ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))))))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))]

theorem candidates26_coefficients : ∀ t ∈ candidates26,
    coefficients (R := GaussianZ) ⟨1,-1⟩ ⟨0,1⟩ 1 t = ⟨1,0,0,⟨-1,2⟩⟩ := by decide

/-- The 28-operation pair differs only by swapping y and z. Its unrestricted
converse is refuted in `Equation872CubicCounterexample`. -/
def candidates28 : List (FreeMagma (Fin 3)) := [
  -- 35462
  (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ ((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ Lf 0))))) ⋆ (Lf 2 ⋆ Lf 0))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))),
  -- 36391
  (((Lf 2 ⋆ Lf 0) ⋆ (((Lf 2 ⋆ Lf 0) ⋆ (Lf 2 ⋆ Lf 0)) ⋆ (Lf 2 ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ ((Lf 1 ⋆ Lf 0) ⋆ (((Lf 1 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) ⋆ (Lf 1 ⋆ Lf 0))))) ⋆ (Lf 1 ⋆ Lf 0))) ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))))) ⋆ (Lf 2 ⋆ (Lf 2 ⋆ Lf 0)))]

theorem candidates28_coefficients : ∀ t ∈ candidates28,
    coefficients (R := GaussianZ) ⟨1,-1⟩ ⟨0,1⟩ 1 t = ⟨1,0,0,⟨2,1⟩⟩ := by decide

include hi
/-- In this entire affine family the remaining 26-operation candidates are
exact, even with arbitrary commutative coefficient rings. This does not claim
an unrestricted single-equation characterization. -/
theorem candidates26_iff (t : FreeMagma (Fin 3)) (ht : t ∈ candidates26) :
    @satisfies _ R (magma i) (identity t) ↔ InImage Law872 .left (magma i) := by
  rw [identity_iff_constant i hi t (-1) 2 (candidates26_coefficients t ht), image_iff i hi]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- The 28-operation candidates have the same restricted characterization. -/
theorem candidates28_iff (t : FreeMagma (Fin 3)) (ht : t ∈ candidates28) :
    @satisfies _ R (magma i) (identity t) ↔ InImage Law872 .left (magma i) := by
  rw [identity_iff_constant i hi t 2 1 (candidates28_coefficients t ht), image_iff i hi]
  push_cast
  constructor
  · intro h
    linear_combination i*h-hi
  · intro h
    linear_combination -i*h+2*hi

end Parastrophes.Eq872GaussianAffine
