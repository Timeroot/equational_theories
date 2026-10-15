import equational_theories.Spectrum.Equation1110.OrderThirteen.Exclusion
import equational_theories.Spectrum.Equation167
import equational_theories.Spectrum.Generated.NoteBounds

/-! Nine spectrum inclusions are refuted by the newly excluded order thirteen.
Each source has an existing Lean-checked model of that order. -/
namespace Spectrum.E1110.OrderThirteen

theorem not_subspectral_167_1110 : ¬ Law167.Subspectral Law1110 := by
  have hp : Law167.HasModel 13 := models_167 (by norm_num [residues])
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_167_1110 complete

theorem not_subspectral_467_1110 : ¬ Law467.Subspectral Law1110 := by
  have hp : Law467.HasModel 13 := (Note.finite_467 (by simp)).2
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_467_1110 complete

theorem not_subspectral_677_1110 : ¬ Law677.Subspectral Law1110 := by
  have hp : Law677.HasModel 13 := (Note.finite_677 (by simp)).2
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_677_1110 complete

theorem not_subspectral_704_1110 : ¬ Law704.Subspectral Law1110 := by
  have hp : Law704.HasModel 13 := (Note.finite_704 (by simp)).2
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_704_1110 complete

theorem not_subspectral_1076_1110 : ¬ Law1076.Subspectral Law1110 := by
  have hp : Law1076.HasModel 13 := (Note.finite_1076 (by simp)).2
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_1076_1110 complete

theorem not_subspectral_1286_1110 : ¬ Law1286.Subspectral Law1110 := by
  have hp : Law1286.HasModel 13 := (Note.finite_1286 (by simp)).2
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_1286_1110 complete

theorem not_subspectral_1313_1110 : ¬ Law1313.Subspectral Law1110 := by
  have hp : Law1313.HasModel 13 := (Note.finite_1313 (by simp)).2
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_1313_1110 complete

theorem not_subspectral_1486_1110 : ¬ Law1486.Subspectral Law1110 := by
  have hp : Law1486.HasModel 13 := (Note.lower_1486 (by norm_num [positiveExcept])).2
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_1486_1110 complete

theorem not_subspectral_1516_1110 : ¬ Law1516.Subspectral Law1110 := by
  have hp : Law1516.HasModel 13 := (Note.finite_1516 (by simp)).2
  exact fun h => not_order_1110_13 (h.hasModel hp)

spectrum_assert not_subspectral_1516_1110 complete

end Spectrum.E1110.OrderThirteen
