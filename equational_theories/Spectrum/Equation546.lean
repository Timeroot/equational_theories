import equational_theories.Spectrum.GaussianModels
import equational_theories.Spectrum.GaussianRepresentation
import equational_theories.Spectrum.GaussianCardinality

/-! # The exact spectrum of E546: the positive sums of two squares -/

namespace Spectrum
open Law Law.MagmaLaw

theorem card_of_equation546 {G : Type*} [Fintype G] [Magma G]
    (h : Equation546 G) (a : G) : ∃ k l : ℕ, Fintype.card G = k^2 + l^2 := by
  letI := GaussianRepresentation.group h a
  let J := (GaussianRepresentation.rotationEquiv h a).toMultiplicative
  have hJ (x : Multiplicative G) : J (J x) = x⁻¹ := by
    exact congrArg Multiplicative.ofAdd (GaussianRepresentation.rotation_sq h a x.toAdd)
  have hc := GaussianCardinality.card_sum_two_squares J hJ
  rwa [Fintype.card_congr (Multiplicative.toAdd : Multiplicative G ≃ G)] at hc

theorem orders_546 {n : ℕ} (h : n ∈ Law546.spectrum) : n ∈ sumTwoSquares := by
  obtain ⟨hn,M,hM⟩ := h
  letI := M
  have he : Equation546 (Fin n) := (@Law546.models_iff _ M).mp hM
  have hc := card_of_equation546 he ⟨0,hn⟩
  rw [Fintype.card_fin] at hc
  exact ⟨hn,hc⟩

theorem exact_546 : Law546.spectrum = sumTwoSquares := by
  ext n
  exact ⟨orders_546, fun h => ⟨h.1, models_546 h⟩⟩

spectrum_assert exact_546 complete
end Spectrum
