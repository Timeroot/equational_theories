import equational_theories.Spectrum.Shapes
import equational_theories.Spectrum.Status
import equational_theories.Equations.All
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-! # Gaussian models at every sum of two squares -/

namespace Spectrum
open Law Law.MagmaLaw

@[implicit_reducible] def gaussianMagma {G : Type*} [AddCommGroup G] (J : G →+ G) : Magma G :=
  ⟨fun x y => -x + J y⟩

theorem gaussian_equation546 {G : Type*} [AddCommGroup G] (J : G →+ G)
    (hJ : ∀ x, J (J x) = -x) : @Equation546 G (gaussianMagma J) := by
  intro x y z
  change x = -y + J (-z + J (-x + J (-z + J y)))
  simp only [map_add, map_neg, hJ, neg_neg]
  abel

theorem square_model_546 (a : ℕ) [NeZero a] : Law546.HasModel (a^2) := by
  let J : ZMod a × ZMod a →+ ZMod a × ZMod a := {
    toFun := fun x => (-x.2,x.1)
    map_zero' := by simp
    map_add' := by intro x y; ext <;> simp [neg_add_rev, add_comm] }
  have hJ (x : ZMod a × ZMod a) : J (J x) = -x := by ext <;> simp [J]
  exact hasModel_of_card (gaussianMagma J)
    ((@Law546.models_iff _ (gaussianMagma J)).mpr (gaussian_equation546 J hJ))
    (by simp [pow_two])

theorem modular_model_546 (b : ℕ) [NeZero b] (h : IsSquare (-1 : ZMod b)) :
    Law546.HasModel b := by
  obtain ⟨r,hr⟩ := h
  let J : ZMod b →+ ZMod b := {
    toFun := fun x => r*x
    map_zero' := mul_zero r
    map_add' := mul_add r }
  have hJ (x : ZMod b) : J (J x) = -x := by
    change r*(r*x) = -x
    rw [← mul_assoc, ← hr, neg_one_mul]
  exact hasModel_of_card (gaussianMagma J)
    ((@Law546.models_iff _ (gaussianMagma J)).mpr (gaussian_equation546 J hJ))
    (ZMod.card b)

theorem models_546 {n : ℕ} (h : n ∈ sumTwoSquares) : Law546.HasModel n := by
  obtain ⟨hn,hs⟩ := h
  obtain ⟨a,b,rfl,hb⟩ := Nat.eq_sq_add_sq_iff_eq_sq_mul.mp hs
  haveI : NeZero a := ⟨by intro ha; simp [ha] at hn⟩
  haveI : NeZero b := ⟨by intro hb; simp [hb] at hn⟩
  exact (square_model_546 a).mul (modular_model_546 b hb)

spectrum_assert models_546 complete
end Spectrum
