import equational_theories.Spectrum.GaussianModels

/-! # Odd Gaussian models for E467

The operation is `x ◇ y = -(1+i)x/2 + iy`. Decomposing a sum of two
squares as `a²*b` lets us use a rotation on `(ZMod a)²` and a square
root of minus one on `ZMod b`, avoiding quotient cardinality calculations.
-/

namespace Spectrum
open Law Law.MagmaLaw

@[implicit_reducible] def twistedGaussianMagma {R G : Type*} [CommRing R]
    [AddCommGroup G] [Module R G] (t : R) (J : G →ₗ[R] G) : Magma G :=
  ⟨fun x y => -t • (x + J x) + J y⟩

theorem twistedGaussian_equation467 {R G : Type*} [CommRing R]
    [AddCommGroup G] [Module R G] (t : R) (J : G →ₗ[R] G)
    (ht : t + t = 1) (hJ : ∀ x, J (J x) = -x) :
    @Equation467 G (twistedGaussianMagma t J) := by
  intro x y
  change x = -t • (y + J y) + J (-t • (x + J x) +
    J (-t • (x + J x) + J (-t • (y + J y) + J y)))
  simp only [map_add, map_smul, hJ, map_neg, neg_neg]
  trans (t + t) • x - (t + t) • y + y
  · rw [ht]; simp
  · module

def oddHalf (n : ℕ) (hn : Odd n) : ZMod n :=
  ↑((ZMod.unitOfCoprime 2 hn.coprime_two_left)⁻¹)

theorem oddHalf_add (n : ℕ) (hn : Odd n) : oddHalf n hn + oddHalf n hn = 1 := by
  have h := (ZMod.unitOfCoprime 2 hn.coprime_two_left).mul_inv
  change (ZMod.unitOfCoprime 2 hn.coprime_two_left : ZMod n) * oddHalf n hn = 1 at h
  simpa only [ZMod.coe_unitOfCoprime, Nat.cast_ofNat, two_mul] using h

theorem odd_square_model_467 (a : ℕ) [NeZero a] (ha : Odd a) :
    Law467.HasModel (a ^ 2) := by
  let J : (ZMod a × ZMod a) →ₗ[ZMod a] (ZMod a × ZMod a) := {
    toFun := fun x => (-x.2, x.1)
    map_add' := by intro x y; ext <;> simp [neg_add_rev, add_comm]
    map_smul' := by intro r x; ext <;> simp }
  have hJ (x : ZMod a × ZMod a) : J (J x) = -x := by ext <;> simp [J]
  exact hasModel_of_card (twistedGaussianMagma (oddHalf a ha) J)
    ((@Law467.models_iff _ (twistedGaussianMagma (oddHalf a ha) J)).mpr
      (twistedGaussian_equation467 _ J (oddHalf_add a ha) hJ)) (by simp [pow_two])

theorem odd_modular_model_467 (b : ℕ) [NeZero b] (hb : Odd b)
    (h : IsSquare (-1 : ZMod b)) : Law467.HasModel b := by
  obtain ⟨r, hr⟩ := h
  let J : ZMod b →ₗ[ZMod b] ZMod b := {
    toFun := fun x => r*x
    map_add' := mul_add r
    map_smul' := by intro s x; simp [mul_left_comm] }
  have hJ (x : ZMod b) : J (J x) = -x := by
    change r*(r*x) = -x
    rw [← mul_assoc, ← hr, neg_one_mul]
  exact hasModel_of_card (twistedGaussianMagma (oddHalf b hb) J)
    ((@Law467.models_iff _ (twistedGaussianMagma (oddHalf b hb) J)).mpr
      (twistedGaussian_equation467 _ J (oddHalf_add b hb) hJ)) (ZMod.card b)

theorem odd_sums_467 : oddSumTwoSquares ⊆ Law467.spectrum := by
  rintro n ⟨k, l, rfl⟩
  have hn : 0 < (2*k)^2 + (2*l+1)^2 := by positivity
  have ho : Odd ((2*k)^2 + (2*l+1)^2) := by
    rw [Nat.odd_iff]
    simp [Nat.add_mod, Nat.pow_mod]
  obtain ⟨a, b, hab, hb⟩ := Nat.eq_sq_add_sq_iff_eq_sq_mul.mp ⟨2*k, 2*l+1, rfl⟩
  rw [hab] at hn ho ⊢
  haveI : NeZero a := ⟨by intro ha; simp [ha] at hn⟩
  haveI : NeZero b := ⟨by intro hb; simp [hb] at hn⟩
  have ha : Odd a := (Nat.odd_pow_iff (by decide : 2 ≠ 0)).mp (Nat.odd_mul.mp ho).1
  exact ⟨hn, (odd_square_model_467 a ha).mul (odd_modular_model_467 b ((Nat.odd_mul.mp ho).2) hb)⟩

spectrum_assert odd_sums_467 complete
end Spectrum
