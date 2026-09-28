import equational_theories.Spectrum.DupontTwists
import equational_theories.Spectrum.QuarticSeeds

/-! Named lower bounds for the open catalogue. These expose the entire proved
idempotent E63 construction, not just its eventual tail or a few small seeds. -/

namespace Spectrum.OpenConstructions

theorem dupont {n : ℕ} (hn : n ∉ E63.FieldBounds.remaining) :
    Law467.HasModel n ∧ Law704.HasModel n ∧ Law1110.HasModel n ∧
    Law1279.HasModel n ∧ Law1516.HasModel n :=
  DupontTwists.models (E63.FieldBounds.model hn)

theorem cubes_all {n : ℕ} (hn : n ∈ cubes) :
    Law467.HasModel n ∧ Law704.HasModel n ∧ Law1110.HasModel n ∧
    Law1279.HasModel n ∧ Law1516.HasModel n := by
  obtain ⟨hpos, k, rfl⟩ := hn
  have hk : k ≠ 0 := by rintro rfl; simp at hpos
  letI : NeZero k := ⟨hk⟩
  exact DupontTwists.models (E63.cubic_idempotent k)

theorem fourth_670 : fourthPowers ⊆ Law670.spectrum := by
  rintro n ⟨hpos, k, rfl⟩
  have hk : k ≠ 0 := by rintro rfl; simp at hpos
  letI : NeZero k := ⟨hk⟩
  exact ⟨hpos, QuarticSeeds.model_670 k⟩

theorem fourth_677 : fourthPowers ⊆ Law677.spectrum := by
  rintro n ⟨hpos, k, rfl⟩
  have hk : k ≠ 0 := by rintro rfl; simp at hpos
  letI : NeZero k := ⟨hk⟩
  exact ⟨hpos, QuarticSeeds.model_677 k⟩

theorem fourth_1076 : fourthPowers ⊆ Law1076.spectrum := by
  rintro n ⟨hpos, k, rfl⟩
  have hk : k ≠ 0 := by rintro rfl; simp at hpos
  letI : NeZero k := ⟨hk⟩
  exact ⟨hpos, QuarticSeeds.model_1076 k⟩

theorem fourth_1286 : fourthPowers ⊆ Law1286.spectrum := by
  rintro n ⟨hpos, k, rfl⟩
  have hk : k ≠ 0 := by rintro rfl; simp at hpos
  letI : NeZero k := ⟨hk⟩
  exact ⟨hpos, QuarticSeeds.model_1286 k⟩

theorem fourth_1313 : fourthPowers ⊆ Law1313.spectrum := by
  rintro n ⟨hpos, k, rfl⟩
  have hk : k ≠ 0 := by rintro rfl; simp at hpos
  letI : NeZero k := ⟨hk⟩
  exact ⟨hpos, QuarticSeeds.model_1313 k⟩

end Spectrum.OpenConstructions
