import equational_theories.Parastrophes.Basic
import Mathlib.Tactic.Ring

/-! A small symbolic checker for three-variable identities of affine magmas.
It computes four coefficients, not a multiplication table or all assignments. -/
namespace Parastrophes.AffineIdentityCertificate
open Law FreeMagma

@[ext] structure Coefficients (R : Type) where
  x : R
  y : R
  z : R
  constant : R
  deriving DecidableEq

def coefficients {R : Type} [CommRing R] (p q s : R) :
    FreeMagma (Fin 3) → Coefficients R
  | .Leaf i => if i = 0 then ⟨1,0,0,0⟩ else if i = 1 then ⟨0,1,0,0⟩ else ⟨0,0,1,0⟩
  | .Fork a b =>
    let u := coefficients p q s a
    let v := coefficients p q s b
    ⟨p*u.x+q*v.x, p*u.y+q*v.y, p*u.z+q*v.z, p*u.constant+q*v.constant+s⟩

@[implicit_reducible] def affine {R : Type} [CommRing R] (p q s : R) : Magma R :=
  ⟨fun x y => p*x+q*y+s⟩

@[simp] theorem affine_op {R : Type} [CommRing R] (p q s x y : R) :
    (affine p q s).op x y = p*x+q*y+s := rfl

def value {R : Type} [CommRing R] (c : Coefficients R) (v : Fin 3 → R) : R :=
  c.x*v 0 + c.y*v 1 + c.z*v 2 + c.constant

def Coefficients.map {R S : Type} (f : R → S) (c : Coefficients R) : Coefficients S :=
  ⟨f c.x, f c.y, f c.z, f c.constant⟩

/-- Compute a certificate once in a universal ring, then specialize it. -/
theorem coefficients_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (p q s : R) (t : FreeMagma (Fin 3)) :
    coefficients (f p) (f q) (f s) t = (coefficients p q s t).map f := by
  induction t with
  | Leaf i => fin_cases i <;> simp [coefficients, Coefficients.map]
  | Fork a b ha hb => simp [coefficients, ha, hb, Coefficients.map]

theorem quasigroup_fin {R : Type} [CommRing R] [Finite R] (p q s : R)
    (hp : IsUnit p) (hq : IsUnit q) : IsQuasigroup (affine p q s) := by
  constructor
  · intro a
    have hi : Function.Injective ((affine p q s).op a) := by
      intro b c h
      exact hq.mul_left_cancel (add_left_cancel (add_right_cancel h))
    exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩
  · intro b
    have hi : Function.Injective (fun a => (affine p q s).op a b) := by
      intro a c h
      exact hp.mul_left_cancel (add_right_cancel (add_right_cancel h))
    exact ⟨hi, Finite.injective_iff_surjective.mp hi⟩

theorem eval_eq_value {R : Type} [CommRing R] (p q s : R)
    (t : FreeMagma (Fin 3)) (v : Fin 3 → R) :
    @evalInMagma _ R (affine p q s) v t = value (coefficients p q s t) v := by
  induction t with
  | Leaf i => fin_cases i <;> simp [evalInMagma, coefficients, value]
  | Fork a b ha hb =>
    change p * @evalInMagma _ R (affine p q s) v a +
      q * @evalInMagma _ R (affine p q s) v b + s = _
    rw [ha, hb]
    simp only [coefficients, value]
    ring

def identity (t : FreeMagma (Fin 3)) : NatMagmaLaw :=
  ⟨Lf 0, fmapFreeMagma Fin.val t⟩

/-- A coefficient certificate proves the identity on every assignment. -/
theorem satisfies_of_coefficients {R : Type} [CommRing R] (p q s : R)
    (t : FreeMagma (Fin 3)) (h : coefficients p q s t = ⟨1,0,0,0⟩) :
    @satisfies _ R (affine p q s) (identity t) := by
  letI : Magma R := affine p q s
  intro v
  change v 0 = @evalInMagma _ R (affine p q s) v (fmapFreeMagma Fin.val t)
  rw [← evalInMagma_comp, eval_eq_value, h]
  simp [value]

/-- Zero and the three coordinate assignments recover all four coefficients.
This also works over rings with zero divisors and in the zero ring. -/
theorem coefficients_of_satisfies {R : Type} [CommRing R] (p q s : R)
    (t : FreeMagma (Fin 3)) (h : @satisfies _ R (affine p q s) (identity t)) :
    coefficients p q s t = ⟨1,0,0,0⟩ := by
  letI : Magma R := affine p q s
  have he (a b c : R) : a = (coefficients p q s t).x*a +
      (coefficients p q s t).y*b + (coefficients p q s t).z*c +
      (coefficients p q s t).constant := by
    have ht := h (fun n => if n=0 then a else if n=1 then b else c)
    change a = @evalInMagma _ R (affine p q s)
      (fun n => if n=0 then a else if n=1 then b else c) (fmapFreeMagma Fin.val t) at ht
    rw [← evalInMagma_comp, eval_eq_value] at ht
    simpa [value] using ht
  have h0 : (coefficients p q s t).constant=0 := by simpa using (he 0 0 0).symm
  have hx : (coefficients p q s t).x=1 := by simpa [h0] using (he 1 0 0).symm
  have hy : (coefficients p q s t).y=0 := by simpa [h0] using (he 0 1 0).symm
  have hz : (coefficients p q s t).z=0 := by simpa [h0] using (he 0 0 1).symm
  exact Coefficients.ext hx hy hz h0

end Parastrophes.AffineIdentityCertificate
