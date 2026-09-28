import equational_theories.Spectrum.Equation1486.EightNormalization
import equational_theories.Spectrum.Equation1486.EightRefutation

/-! The eight-element exclusion combines a general square-row rank bound,
proved label normalization, and two checked finite refutations. -/
namespace Spectrum

theorem not_order_1486_8 : ¬ Law1486.HasModel 8 := by
  rintro ⟨M, hM⟩
  have h : E1486.SquareRows.Lawful M.op := fun x y z =>
    ((@Law1486.models_iff _ M).mp hM x y z).symm
  obtain ⟨g, inside, _, hg, hi⟩ := E1486.SquareRows.normalize_eight M.op h
  exact FiniteExclusion.E1486N8TwoImages.impossible inside ⟨g⟩
    (fun x y z => (hg x y z).symm) hi

spectrum_assert not_order_1486_8 complete

end Spectrum
