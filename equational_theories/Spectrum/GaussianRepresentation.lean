import equational_theories.Spectrum.GaussianIdentities
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # The affine Gaussian-module representation of E546 -/

namespace Spectrum.GaussianRepresentation
variable {G : Type*} [Magma G]

/-- Choosing an anchor determines an abelian group, with zero `a ◇ a`. -/
@[implicit_reducible] def group (h : Equation546 G) (a : G) : AddCommGroup G := by
  letI : Add G := ⟨addOp a⟩
  letI : Zero G := ⟨a ◇ a⟩
  letI : Neg G := ⟨fun x => turn a (turn a x)⟩
  exact {
    add := addOp a
    zero := a ◇ a
    neg := fun x => turn a (turn a x)
    add_assoc := fun x y z => assoc h a x y z
    zero_add := fun x => zero_add h a x a a
    add_zero := fun x => add_zero h a x a a
    neg_add_cancel := fun x => neg_add h a x a a
    add_comm := fun x y => comm h a x y a
    nsmul := nsmulRec
    zsmul := zsmulRec }

def rotation (h : Equation546 G) (a : G) : letI := group h a; G →+ G := by
  letI := group h a
  exact {
    toFun := turn a
    map_zero' := j_zero h a a a a
    map_add' := fun x y => j_add h a x y a }

theorem rotation_sq (h : Equation546 G) (a x : G) :
    letI := group h a
    rotation h a (rotation h a x) = -x := rfl

def rotationEquiv (h : Equation546 G) (a : G) : letI := group h a; G ≃+ G := by
  letI := group h a
  exact {
    toFun := rotation h a
    map_add' := (rotation h a).map_add
    invFun := fun x => -rotation h a x
    left_inv := fun x => by change -(rotation h a (rotation h a x)) = x; rw [rotation_sq, neg_neg]
    right_inv := fun x => by change rotation h a (-rotation h a x) = x; rw [map_neg, rotation_sq, neg_neg] }

/-- The original operation is affine with coefficients `-1` and `i`. -/
theorem affine_formula (h : Equation546 G) (a x y : G) :
    letI := group h a
    x ◇ y = -x + (rotation h a y + ((a ◇ a) ◇ (a ◇ a))) :=
  affine h a x y a

end Spectrum.GaussianRepresentation

namespace Spectrum

/-- An additive square root of negation is exactly the data needed for the
action of the Gaussian integers. -/
@[implicit_reducible] def gaussianModule {G : Type*} [AddCommGroup G]
    (J : G →+ G) (hJ : ∀ x, J (J x) = -x) : Module GaussianInt G where
  smul r x := r.re • x + r.im • J x
  one_smul x := by
    change (1 : GaussianInt).re • x + (1 : GaussianInt).im • J x = x
    simp
  mul_smul r s x := by
    change ((r*s).re • x + (r*s).im • J x) =
      r.re • (s.re • x + s.im • J x) + r.im • J (s.re • x + s.im • J x)
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, add_zsmul, mul_zsmul, smul_add,
      map_add, map_zsmul, hJ, neg_one_mul, neg_zsmul, zsmul_neg]
    abel
  smul_zero r := by
    change r.re • (0 : G) + r.im • J 0 = 0
    simp
  smul_add r x y := by
    change r.re • (x+y) + r.im • J (x+y) = (r.re • x + r.im • J x) + (r.re • y + r.im • J y)
    simp [smul_add, map_add]
    abel
  add_smul r s x := by
    change (r+s).re • x + (r+s).im • J x = (r.re • x + r.im • J x) + (s.re • x + s.im • J x)
    simp [add_zsmul]
    abel
  zero_smul x := by
    change (0 : GaussianInt).re • x + (0 : GaussianInt).im • J x = 0
    simp

/-- The full Gaussian-module structure reconstructed from a nonempty E546 model. -/
@[implicit_reducible] def GaussianRepresentation.module {G : Type*} [Magma G]
    (h : Equation546 G) (a : G) : letI := GaussianRepresentation.group h a; Module GaussianInt G := by
  letI := GaussianRepresentation.group h a
  exact gaussianModule (GaussianRepresentation.rotation h a)
    (GaussianRepresentation.rotation_sq h a)

end Spectrum
