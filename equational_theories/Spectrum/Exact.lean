import equational_theories.Spectrum.Constructions
import equational_theories.Spectrum.Generated.NotTwo1501
import equational_theories.Spectrum.Generated.Two
import equational_theories.Spectrum.Generated.SmallExclusions
import equational_theories.Spectrum.Generated.NotTwo0001
import equational_theories.Duals.All

/-! Exact and infinite-family results beyond the full-spectrum classification. -/

open Law Law.MagmaLaw

namespace Spectrum

theorem spectrum_474 : Law474.spectrum = {n | 0 < n ∧ n ≠ 2 ∧ n ≠ 4} := by
  ext n
  constructor
  · rintro ⟨hn, hM⟩
    refine ⟨hn, ?_, ?_⟩
    · rintro rfl; exact not_two_474 hM
    · rintro rfl; exact not_order_474_4 hM
  · rintro ⟨hn, h2, h4⟩
    exact ⟨hn, hasModel_474_of_not_two_four n h2 h4⟩

/-- Table (15) and the odd-order construction cover every size except two. -/
theorem hasModel_1685_iff (n : ℕ) : Law1685.HasModel n ↔ n ≠ 2 := by
  constructor
  · intro h hn
    subst n
    exact not_two_1685 h
  · intro hn
    by_cases hz : n = 0
    · subst n; exact Law1685.hasModel_zero
    · by_cases ho : n % 2 = 1
      · convert odd_1685 (n / 2) using 1; omega
      · have he : n % 2 = 0 := by omega
        convert even_1685 ((n - 4) / 2) using 1; omega

theorem spectrum_1685 : Law1685.spectrum = {n | 0 < n ∧ n ≠ 2} := by
  ext n
  simp [hasModel_1685_iff]

theorem spectrum_1922 : Law1922.spectrum = {n | 0 < n ∧ n ≠ 2} :=
  (spectrum_eq_of_isDual dual_1922).trans spectrum_1685

/-- All squares and twice all squares occur for E1485; the converse is UNKNOWN here. -/
theorem twice_square_1485 (k : ℕ) : Law1485.HasModel (2 * k ^ 2) :=
  two_1485.mul (square_1485 k)

/-- Boolean addition supplies all powers of two for E895.
The upper bound, although known mathematically, is not formalized in this module. -/
theorem power_two_895 (k : ℕ) : Law895.HasModel (2 ^ k) := two_895.pow k

theorem power_two_898 (k : ℕ) : Law898.HasModel (2 ^ k) := two_898.pow k

end Spectrum
