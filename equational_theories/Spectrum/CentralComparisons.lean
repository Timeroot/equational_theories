import equational_theories.Spectrum.Constructions
import equational_theories.Spectrum.Generated.Two
import equational_theories.Spectrum.Generated.SmallOrder

/-!
Additional spectrum bounds for the remaining central-law comparisons.
E1483 contains every square and twice-square order. E1486 has no model of
order three, in addition to the previously checked exclusion of order two.
These are spectrum results, not assertions of definability between the laws.
-/

namespace Spectrum

theorem twiceSquare_1483 (k : ℕ) : Law1483.HasModel (2 * k ^ 2) :=
  Law.MagmaLaw.HasModel.mul two_1483 (square_1483 k)

@[spectrum_native]
theorem not_three_1486 : ¬ Law1486.HasModel 3 :=
  not_three_of_equation Law1486 (@Equation1486 (Fin 3))
    (@Law1486.models_iff (Fin 3)) (by native_decide)

spectrum_assert twiceSquare_1483 complete
spectrum_assert not_three_1486 complete

/-- If the proposed upper bound for E1485 is exact, its spectrum is contained
in E1483's spectrum, so cardinality cannot refute this direction. -/
theorem spectrum_1485_subset_1483_of_square_bound
    (h : ∀ n ∈ Law1485.spectrum, ∃ k, n = k ^ 2 ∨ n = 2 * k ^ 2) :
    Law1485.spectrum ⊆ Law1483.spectrum := by
  intro n hn
  obtain ⟨k, hk | hk⟩ := h n hn
  · exact ⟨hn.1, hk ▸ square_1483 k⟩
  · exact ⟨hn.1, hk ▸ twiceSquare_1483 k⟩

/-- The proposed cofinite lower bound for E1480 would contain every E1486
order. The hypothesis is deliberately retained: this is a conditional result. -/
theorem spectrum_1486_subset_1480_of_cofinite_bound
    (h : ∀ n, 4 ≤ n → Law1480.HasModel n) :
    Law1486.spectrum ⊆ Law1480.spectrum := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  have htwo : n ≠ 2 := fun he => not_two_1486 (he ▸ hn.2)
  have hthree : n ≠ 3 := fun he => not_three_1486 (he ▸ hn.2)
  by_cases hone : n = 1
  · exact hone ▸ Law.MagmaLaw.hasModel_one Law1480
  · have hpos : 0 < n := hn.1
    exact h n (by omega)

end Spectrum
