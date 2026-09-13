import equational_theories.Spectrum.Basic
import equational_theories.FullSpectrum
import equational_theories.Duals.All

/-! Reuse the established full-spectrum constructions, including their duals. -/

open Law Law.MagmaLaw

namespace Spectrum

theorem full_iff_equation (L : NatMagmaLaw) (E : (G : Type) → Magma G → Prop)
    (h : ∀ n M, @satisfies _ (Fin n) M L ↔ E (Fin n) M) :
    L.HasFullSpectrum ↔ FullSpectrum.EqFullSpectrum E := by
  constructor
  · intro hL n
    obtain ⟨M, hM⟩ := hL n
    exact ⟨M, (h n M).mp hM⟩
  · intro hE n
    obtain ⟨M, hM⟩ := hE n
    exact ⟨M, (h n M).mpr hM⟩

theorem full_1482 : Law1482.HasFullSpectrum :=
  (full_iff_equation Law1482 (@Equation1482) (fun _ _ => Law1482.models_iff)).mpr
    FullSpectrum.full_spectrum_Equation1482

theorem full_1523 : Law1523.HasFullSpectrum :=
  (full_iff_equation Law1523 (@Equation1523) (fun _ _ => Law1523.models_iff)).mpr
    FullSpectrum.full_spectrum_square_cancellative

theorem full_1682 : Law1682.HasFullSpectrum :=
  (full_iff_equation Law1682 (@Equation1682) (fun _ _ => Law1682.models_iff)).mpr
    FullSpectrum.full_spectrum_Equation1682

private theorem full_of_isDual {L K : NatMagmaLaw} (h : L.IsDual K)
    (hL : L.HasFullSpectrum) : K.HasFullSpectrum := by
  rw [hasFullSpectrum_iff_spectrum] at hL ⊢
  rwa [← spectrum_eq_of_isDual h]

theorem full_1885 : Law1885.HasFullSpectrum := full_of_isDual dual_1682 full_1682
theorem full_2125 : Law2125.HasFullSpectrum := full_of_isDual dual_1482 full_1482
theorem full_2132 : Law2132.HasFullSpectrum := full_of_isDual dual_1523 full_1523

theorem spectrum_two : Law2.spectrum = {1} := by
  ext n
  constructor
  · rintro ⟨hn, M, hM⟩
    have h := (@Law2.models_iff (Fin n) M).mp hM
    have hle : n ≤ 1 := by
      by_contra! hn'
      have h01 := h ⟨0, by omega⟩ ⟨1, by omega⟩
      have := congrArg Fin.val h01
      change (0 : ℕ) = 1 at this
      omega
    simpa using (show n = 1 by omega)
  · rintro rfl
    exact Law2.one_mem_spectrum

theorem singleton_of_implies {L : NatMagmaLaw} (h : L.implies Law2) : L.spectrum = {1} := by
  apply Set.Subset.antisymm
  · rw [← spectrum_two]
    exact subspectral_of_implies h
  · rintro n rfl
    exact L.one_mem_spectrum

end Spectrum
