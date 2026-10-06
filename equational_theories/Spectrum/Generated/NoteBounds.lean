import equational_theories.Spectrum.Note
import equational_theories.Spectrum.Equation63
import equational_theories.Spectrum.Generated
import equational_theories.Spectrum.OpenConstructions
import equational_theories.Spectrum.OpenWitnesses
import equational_theories.Spectrum.Equation1516Bounds
import equational_theories.Spectrum.SmallPairs
import equational_theories.Spectrum.Equation467.OrderSixteen.Exclusion
import equational_theories.Spectrum.Equation907.OddTail
import equational_theories.Spectrum.Equation907Eight
import equational_theories.Spectrum.Equation677.Small
import equational_theories.Spectrum.Equation677.OrderSix
import equational_theories.Spectrum.Equation677.EffectiveTail
import equational_theories.Spectrum.Equation677.DesignWitnesses
import equational_theories.Spectrum.Equation1083_1286.Bounds
import equational_theories.Spectrum.Equation1083_1286.BinaryHalves
import equational_theories.Spectrum.Equation1083.SmallExclusions
import equational_theories.Definability.Central1483OrderEleven
import equational_theories.Spectrum.QuadraticSeeds
import equational_theories.Spectrum.Equation667883ExtendedBounds
import equational_theories.Spectrum.Equation667883Small
import equational_theories.Spectrum.Equation667Twelve.Exclusion
import equational_theories.Spectrum.Equation883Nine
import equational_theories.Spectrum.Equation1483
import equational_theories.Spectrum.Equation1486.FiniteBounds
import equational_theories.Spectrum.Equation1486.Exclusions
import equational_theories.Spectrum.WeakCentralCardinality
import equational_theories.Spectrum.Generated.NoteWitnesses
import equational_theories.Spectrum.Generated.NoteObligations
import equational_theories.Spectrum.Generated.NoteExclusions

/-! Every lower bound, initial segment, and undisputed cofinite claim of §3.
UNKNOWN exact spectra are intentionally represented by bounds, not equalities.
Some statements depend on the explicitly named Pending obligations. -/

open Law Law.MagmaLaw
namespace Spectrum.Note

private theorem dupont_exceptions_eq : E63.ExtendedBounds.remaining = {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 128, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 300, 340, 346, 349, 356, 422, 426, 439, 487, 499, 508, 516, 520, 534, 538, 542, 548, 674, 688} := by decide +kernel

-- UNKNOWN: the exact spectrum of E63 is not established in the note.
theorem finite_63 : ({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ) ⊆ Law63.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law63.hasModel_one⟩
  · exact ⟨by decide, model_63_3⟩
  · exact ⟨by decide, NoteWitness.model_63_4⟩
  · exact ⟨by decide, model_63_5⟩
  · exact ⟨by decide, model_63_7⟩
  · exact ⟨by decide, NoteWitness.model_63_8⟩
  · exact ⟨by decide, (model_63_3.mul model_63_3)⟩
  · exact ⟨by decide, model_63_11⟩
  · exact ⟨by decide, (NoteWitness.model_63_4.mul model_63_3)⟩
  · exact ⟨by decide, model_63_13⟩

theorem lower_63 : (positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}) ⊆ Law63.spectrum := E63.lower

theorem upper_63 : Law63.spectrum ⊆ positiveExcept {2, 6, 10, 14} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_two_63 hn.2
  · exact (NegativeTransfer.route_63_6).not_hasModel not_order_63_6 hn.2
  · exact not_order_63_10 hn.2
  · exact Pending.not_order_63_14 hn.2

theorem cofinite_63 : CofiniteSpectrum Law63 := Pending.cofinite_63

-- Historical note bounds; the exact spectrum of E115 is now proved.
theorem finite_115 : ({1, 5} : Set ℕ) ⊆ Law115.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl
  · exact ⟨by decide, Law115.hasModel_one⟩
  · exact ⟨by decide, model_115_5⟩

theorem family_115 : (residues 3 {0, 1} {6}) ⊆ Law115.spectrum := by
  exact Pending.mendelsohn_115

theorem lower_115 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law115.spectrum :=
  Set.union_subset finite_115 family_115

theorem upper_115 : Law115.spectrum ⊆ positiveExcept {2, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact not_two_115 hn.2
  · exact (NegativeTransfer.route_115_6).not_hasModel not_order_873_6 hn.2

-- UNKNOWN: the exact spectrum of E467 is not established in the note.
theorem finite_467 : ({1, 5, 7, 8, 11, 13} : Set ℕ) ⊆ Law467.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law467.hasModel_one⟩
  · exact ⟨by decide, model_467_5⟩
  · exact ⟨by decide, model_467_7⟩
  · exact ⟨by decide, NoteWitness.model_467_8⟩
  · exact ⟨by decide, model_467_11⟩
  · exact ⟨by decide, model_467_13⟩

theorem family_467 : (oddSumTwoSquares) ⊆ Law467.spectrum := by
  exact Pending.odd_sums_467
theorem lower_467 : ((({1, 5, 7, 8, 11, 13} : Set ℕ) ∪ (oddSumTwoSquares)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 128, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 300, 340, 346, 349, 356, 422, 426, 439, 487, 499, 508, 516, 520, 534, 538, 542, 548, 674, 688}) ∪ cubes) ⊆ Law467.spectrum := by
  apply Set.union_subset
  · apply Set.union_subset
    · exact Set.union_subset finite_467 family_467
    · rintro n ⟨hn, he⟩
      have hx : n ∉ E63.ExtendedBounds.remaining := by simpa only [dupont_exceptions_eq] using he
      exact ⟨hn, (DupontTwists.models (E63.ExtendedBounds.model hx)).1⟩
  · intro n hn; exact ⟨hn.1, (OpenConstructions.cubes_all hn).1⟩

theorem upper_467 : Law467.spectrum ⊆ positiveExcept {2, 3, 4, 6, 16} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_467 hn.2
  · exact NoteExclusion.not_three_467 hn.2
  · exact (NegativeTransfer.route_467_4).not_hasModel not_order_467_4 hn.2
  · exact (NegativeTransfer.route_467_6).not_hasModel not_order_467_6 hn.2
  · exact not_order_467_16 hn.2

theorem cofinite_467 : CofiniteSpectrum Law467 := Pending.cofinite_467

-- Historical note bounds; the exact spectrum of E481 is now proved.
theorem finite_481 : ({1, 7, 9, 12, 15} : Set ℕ) ⊆ Law481.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law481.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_481_7⟩
  · exact ⟨by decide, NoteWitness.model_481_9⟩
  · exact ⟨by decide, NoteWitness.model_481_12⟩
  · exact ⟨by decide, NoteWitness.model_481_15⟩

theorem family_481 : (residues 3 {1, 2} {7}) ⊆ Law481.spectrum := by
  exact Pending.loops_481

theorem lower_481 : (({1, 7, 9, 12, 15} : Set ℕ) ∪ (residues 3 {1, 2} {7})) ⊆ Law481.spectrum :=
  Set.union_subset finite_481 family_481

theorem upper_481 : Law481.spectrum ⊆ positiveExcept {3, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact not_three_481 hn.2
  · exact (NegativeTransfer.route_481_6).not_hasModel not_order_481_6 hn.2

-- Historical note bounds; the exact spectrum of E501 is now proved.
theorem finite_501 : ({1, 4, 5, 8, 9} : Set ℕ) ⊆ Law501.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law501.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_501_4⟩
  · exact ⟨by decide, model_501_5⟩
  · exact ⟨by decide, NoteWitness.model_501_8⟩
  · exact ⟨by decide, NoteWitness.model_501_9⟩

theorem lower_501 : (({1, 4, 5, 8, 9} : Set ℕ)) ⊆ Law501.spectrum := finite_501

theorem upper_501 : Law501.spectrum ⊆ positiveExcept {2} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_singleton] at he
  subst n
  exact not_two_501 hn.2

-- UNKNOWN: the exact spectrum of E667 is not established in the note.
theorem finite_667 : ({1, 2, 5, 7, 9, 11, 13} : Set ℕ) ⊆ Law667.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law667.hasModel_one⟩
  · exact ⟨by decide, two_667⟩
  · exact ⟨by decide, model_667_5⟩
  · exact ⟨by decide, E63.idem7.hasModel667⟩
  · exact ⟨by decide, E667.square_model 3⟩
  · exact ⟨by decide, model_667_11⟩
  · exact ⟨by decide, model_667_13⟩

theorem family_667 : (residues 3 {1, 2} ∅) ⊆ Law667.spectrum := by
  intro n hn
  by_cases he : n = 7
  · subst n; exact ⟨by decide, E63.idem7.hasModel667⟩
  · apply Pending.loops_667
    exact ⟨hn.1, hn.2.1, by simpa using he⟩

theorem lower_667 : (positiveExcept {3, 6, 12, 15, 24, 30, 39, 48, 51, 60, 75, 87, 96, 102, 159, 174, 195, 219}) ⊆ Law667.spectrum :=
  E667.ExtendedBounds.lower

theorem upper_667 : Law667.spectrum ⊆ positiveExcept {3, 6, 12} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact not_three_667 hn.2
  · exact not_order_667_6 hn.2
  · exact not_order_667_12 hn.2

theorem cofinite_667 : CofiniteSpectrum Law667 := Pending.cofinite_667

-- UNKNOWN: the exact spectrum of E670 is not established in the note.
theorem finite_670 : ({1, 4, 5, 9, 11} : Set ℕ) ⊆ Law670.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law670.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_670_4⟩
  · exact ⟨by decide, model_670_5⟩
  · exact ⟨by decide, OpenWitnesses.model_670_9⟩
  · exact ⟨by decide, model_670_11⟩

theorem family_670 : (fourthPowers) ⊆ Law670.spectrum := by
  exact OpenConstructions.fourth_670

theorem lower_670 : (({1, 4, 5, 9, 11} : Set ℕ) ∪ (fourthPowers)) ⊆ Law670.spectrum :=
  Set.union_subset finite_670 family_670

theorem upper_670 : Law670.spectrum ⊆ positiveExcept {2, 3, 6, 7} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_two_670 hn.2
  · exact NoteExclusion.not_three_670 hn.2
  · exact (NegativeTransfer.route_670_6).not_hasModel not_order_670_6 hn.2
  · exact not_order_670_7 hn.2

theorem cofinite_670 : CofiniteSpectrum Law670 := Pending.cofinite_670

-- UNKNOWN: the exact spectrum of E677 is not established in the note.
theorem finite_677 : ({1, 5, 7, 9, 11, 13, 16, 19, 21, 79, 80, 127, 6487, 6493, 6499} : Set ℕ) ⊆ Law677.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law677.hasModel_one⟩
  · exact ⟨by decide, model_677_5⟩
  · exact ⟨by decide, model_677_7⟩
  · exact ⟨by decide, NoteWitness.model_677_9⟩
  · exact ⟨by decide, model_677_11⟩
  · exact ⟨by decide, model_677_13⟩
  · exact ⟨by decide, NoteWitness.model_677_16⟩
  · exact ⟨by decide, E677.model19⟩
  · exact ⟨by decide, E677.EffectiveTail.model21⟩
  · exact ⟨by decide, E677.EffectiveTail.idem79.hasModel⟩
  · exact ⟨by decide, E677.model80⟩
  · exact ⟨by decide, E677.EffectiveTail.model127⟩
  · exact ⟨by decide, E677.model6487⟩
  · exact ⟨by decide, E677.model6493⟩
  · exact ⟨by decide, E677.model6499⟩

theorem family_677 : (fourthPowers) ⊆ Law677.spectrum := by
  exact OpenConstructions.fourth_677

theorem lower_677 : ((({1, 5, 7, 9, 11, 13, 16, 19, 21, 79, 80, 127, 6487, 6493, 6499} : Set ℕ) ∪ (fourthPowers)) ∪ e677CertifiedOrders ∪ Set.Ici 164475) ⊆ Law677.spectrum :=
  Set.union_subset (Set.union_subset (Set.union_subset finite_677 family_677) E677.EffectiveTail.certificate_lower) (fun n hn => ⟨lt_of_lt_of_le (by decide : 0 < 164475) hn, E677.EffectiveTail.all_large n hn⟩)

theorem upper_677 : Law677.spectrum ⊆ positiveExcept {2, 3, 4, 6, 8} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_677 hn.2
  · exact not_order_677_3 hn.2
  · exact not_order_677_4 hn.2
  · exact not_order_677_6 hn.2
  · exact not_order_677_8 hn.2

theorem cofinite_677 : CofiniteSpectrum Law677 := Pending.cofinite_677

-- UNKNOWN: the exact spectrum of E704 is not established in the note.
theorem finite_704 : ({1, 5, 7, 8, 11, 13} : Set ℕ) ⊆ Law704.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law704.hasModel_one⟩
  · exact ⟨by decide, model_704_5⟩
  · exact ⟨by decide, model_704_7⟩
  · exact ⟨by decide, NoteWitness.model_704_8⟩
  · exact ⟨by decide, model_704_11⟩
  · exact ⟨by decide, model_704_13⟩

theorem lower_704 : ((({1, 5, 7, 8, 11, 13} : Set ℕ)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 128, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 300, 340, 346, 349, 356, 422, 426, 439, 487, 499, 508, 516, 520, 534, 538, 542, 548, 674, 688}) ∪ cubes) ⊆ Law704.spectrum := by
  apply Set.union_subset
  · apply Set.union_subset
    · exact finite_704
    · rintro n ⟨hn, he⟩
      have hx : n ∉ E63.ExtendedBounds.remaining := by simpa only [dupont_exceptions_eq] using he
      exact ⟨hn, (DupontTwists.models (E63.ExtendedBounds.model hx)).2.1⟩
  · intro n hn; exact ⟨hn.1, (OpenConstructions.cubes_all hn).2.1⟩

theorem upper_704 : Law704.spectrum ⊆ positiveExcept {2, 3, 4, 6, 9} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_704 hn.2
  · exact NoteExclusion.not_three_704 hn.2
  · exact (NegativeTransfer.route_704_4).not_hasModel not_order_704_4 hn.2
  · exact (NegativeTransfer.route_704_6).not_hasModel not_order_704_6 hn.2
  · exact not_order_704_9 hn.2

theorem cofinite_704 : CofiniteSpectrum Law704 := Pending.cofinite_704

-- Historical note bounds; the exact spectrum of E873 is now proved.
theorem finite_873 : ({1, 5} : Set ℕ) ⊆ Law873.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl
  · exact ⟨by decide, Law873.hasModel_one⟩
  · exact ⟨by decide, model_873_5⟩

theorem family_873 : (residues 3 {0, 1} {6}) ⊆ Law873.spectrum := by
  exact Set.Subset.trans Pending.mendelsohn_115 ImplicationTransfer.path_115_873

theorem lower_873 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law873.spectrum :=
  Set.union_subset finite_873 family_873

theorem upper_873 : Law873.spectrum ⊆ positiveExcept {2, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact not_two_873 hn.2
  · exact (NegativeTransfer.route_873_6).not_hasModel not_order_873_6 hn.2

-- UNKNOWN: the exact spectrum of E883 is not established in the note.
theorem finite_883 : ({1, 2, 4, 5, 7, 8, 11, 13, 16} : Set ℕ) ⊆ Law883.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law883.hasModel_one⟩
  · exact ⟨by decide, two_883⟩
  · exact ⟨by decide, model_883_4⟩
  · exact ⟨by decide, model_883_5⟩
  · exact ⟨by decide, model_883_7⟩
  · exact ⟨by decide, model_883_8⟩
  · exact ⟨by decide, model_883_11⟩
  · exact ⟨by decide, model_883_13⟩
  · exact ⟨by decide, model_883_16⟩

theorem family_883 : (residues 3 {1, 2} ∅) ⊆ Law883.spectrum := by
  intro n hn
  by_cases he : n = 7
  · subst n; exact ⟨by decide, model_883_7⟩
  · apply Pending.loops_883
    exact ⟨hn.1, hn.2.1, by simpa using he⟩

theorem lower_883 : (positiveExcept {3, 6, 9, 12, 15, 18, 24, 30, 39, 48, 51, 60, 75, 87, 96, 99, 102, 153, 159, 174, 195, 207, 219}) ⊆ Law883.spectrum :=
  E883.ExtendedBounds.lower

theorem upper_883 : Law883.spectrum ⊆ positiveExcept {3, 6, 9} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact not_three_883 hn.2
  · exact not_order_883_6 hn.2
  · exact not_order_883_9 hn.2

theorem cofinite_883 : CofiniteSpectrum Law883 := Pending.cofinite_883

-- UNKNOWN: the exact spectrum of E907 is not established in the note.
theorem finite_907 : ({1, 3, 7, 9, 11, 13, 23} : Set ℕ) ⊆ Law907.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law907.hasModel_one⟩
  · exact ⟨by decide, model_907_3⟩
  · exact ⟨by decide, model_907_7⟩
  · exact ⟨by decide, model_907_9⟩
  · exact ⟨by decide, model_907_11⟩
  · exact ⟨by decide, model_907_13⟩
  · exact ⟨by decide, OpenWitnesses.model_907_23⟩

theorem lower_907 : (({1, 3, 7, 9, 11, 13, 23} : Set ℕ)) ⊆ Law907.spectrum := finite_907

theorem upper_907 : Law907.spectrum ⊆ positiveExcept {2, 4, 5, 6, 8} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_907 hn.2
  · exact (NegativeTransfer.route_907_4).not_hasModel not_order_907_4 hn.2
  · exact (NegativeTransfer.route_907_5).not_hasModel not_order_907_5 hn.2
  · exact (NegativeTransfer.route_907_6).not_hasModel not_order_907_6 hn.2
  · exact not_order_907_8 hn.2

-- UNKNOWN: the exact spectrum of E1076 is not established in the note.
theorem finite_1076 : ({1, 5, 13, 16, 17, 19, 23, 25, 31, 43, 47, 53, 59, 67, 71, 73, 79, 80, 81} : Set ℕ) ⊆ Law1076.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1076.hasModel_one⟩
  · exact ⟨by decide, model_1076_5⟩
  · exact ⟨by decide, QuarticTail.small_1076_13⟩
  · exact ⟨by decide, QuarticTail.small_1076_16⟩
  · exact ⟨by decide, QuarticTail.small_1076_17⟩
  · exact ⟨by decide, OpenWitnesses.model_1076_19⟩
  · exact ⟨by decide, QuarticTail.small_1076_23⟩
  · exact ⟨by decide, QuarticTail.small_1076_25⟩
  · exact ⟨by decide, QuarticTail.small_1076_31⟩
  · exact ⟨by decide, QuarticTail.small_1076_43⟩
  · exact ⟨by decide, QuarticTail.small_1076_47⟩
  · exact ⟨by decide, QuarticTail.small_1076_53⟩
  · exact ⟨by decide, QuarticTail.small_1076_59⟩
  · exact ⟨by decide, QuarticTail.small_1076_67⟩
  · exact ⟨by decide, QuarticTail.small_1076_71⟩
  · exact ⟨by decide, QuarticTail.small_1076_73⟩
  · exact ⟨by decide, QuarticTail.small_1076_79⟩
  · exact ⟨by decide, QuarticTail.small_1076_80⟩
  · exact ⟨by decide, QuarticTail.small_1076_81⟩

theorem family_1076 : (fourthPowers) ⊆ Law1076.spectrum := by
  exact OpenConstructions.fourth_1076

theorem lower_1076 : ((({1, 5, 13, 16, 17, 19, 23, 25, 31, 43, 47, 53, 59, 67, 71, 73, 79, 80, 81} : Set ℕ) ∪ (fourthPowers)) ∪ quarticTailSeeds ∪ Set.Ici 107773) ⊆ Law1076.spectrum :=
  Set.union_subset (Set.union_subset (Set.union_subset finite_1076 family_1076) QuarticTail.finite_1076) (fun n hn => ⟨Nat.lt_of_lt_of_le (by decide : 0 < 107773) hn, QuarticTail.model_1076 n hn⟩)

theorem upper_1076 : Law1076.spectrum ⊆ positiveExcept {2, 3, 4, 6, 7} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_1076 hn.2
  · exact NoteExclusion.not_three_1076 hn.2
  · exact (NegativeTransfer.route_1076_4).not_hasModel not_order_1076_4 hn.2
  · exact (NegativeTransfer.route_1076_6).not_hasModel not_order_1076_6 hn.2
  · exact (NegativeTransfer.route_1076_7).not_hasModel not_order_1076_7 hn.2

theorem cofinite_1076 : CofiniteSpectrum Law1076 := Pending.cofinite_1076

-- UNKNOWN: the exact spectrum of E1083 is not established in the note.
theorem finite_1083 : ({1, 3, 4, 7, 8, 9, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 50, 53, 61, 67, 73, 79, 113, 470, 1008, 1009, 1017083} : Set ℕ) ⊆ Law1083.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1083.hasModel_one⟩
  · exact ⟨by decide, model_1083_3⟩
  · exact ⟨by decide, NoteWitness.model_1083_4⟩
  · exact ⟨by decide, model_1083_7⟩
  · exact ⟨by decide, NoteWitness.model_1083_8⟩
  · exact ⟨by decide, model_1083_9⟩
  · exact ⟨by decide, E1083E1286.model_1083_11⟩
  · exact ⟨by decide, model_1083_13⟩
  · exact ⟨by decide, E1083E1286.model_1083_17⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_19⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_23⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_29⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_31⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_37⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_43⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_47⟩
  · exact ⟨by decide, E1083E1286.model_1083_50⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_53⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_61⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_67⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_73⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1083_79⟩
  · exact ⟨by decide, E1083E1286.model_1083_113⟩
  · exact ⟨by decide, E1083E1286.model_1083_470⟩
  · exact ⟨by decide, E1083E1286.model_1083_1008⟩
  · exact ⟨by decide, E1083E1286.model_1083_1009⟩
  · exact ⟨by decide, E1083E1286.model_1083_1017083⟩

theorem family_1083 : (squares ∪ commonPointSquareOrders ∪ designPairOrders) ⊆ Law1083.spectrum := by
  exact E1083E1286.family1083

theorem lower_1083 : (({1, 3, 4, 7, 8, 9, 11, 13, 17, 19, 23, 29, 31, 37, 43, 47, 50, 53, 61, 67, 73, 79, 113, 470, 1008, 1009, 1017083} : Set ℕ) ∪ (squares ∪ commonPointSquareOrders ∪ designPairOrders)) ⊆ Law1083.spectrum :=
  Set.union_subset finite_1083 family_1083

theorem upper_1083 : Law1083.spectrum ⊆ positiveExcept {2, 5, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact not_two_1083 hn.2
  · exact not_order_1083_5 hn.2
  · exact not_order_1083_6 hn.2

theorem cofinite_1083 : CofiniteSpectrum Law1083 := Pending.cofinite_1083

-- UNKNOWN: the exact spectrum of E1110 is not established in the note.
theorem finite_1110 : ({1, 4, 5, 7, 8, 9, 11} : Set ℕ) ⊆ Law1110.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1110.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_1110_4⟩
  · exact ⟨by decide, model_1110_5⟩
  · exact ⟨by decide, model_1110_7⟩
  · exact ⟨by decide, NoteWitness.model_1110_8⟩
  · exact ⟨by decide, NoteWitness.model_1110_9⟩
  · exact ⟨by decide, model_1110_11⟩

theorem family_1110 : (squares) ⊆ Law1110.spectrum := by
  rintro n ⟨hn, k, rfl⟩
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  letI : NeZero k := ⟨hk⟩
  exact ⟨hn, QuadraticSeeds.square1110 k⟩
theorem lower_1110 : ((({1, 4, 5, 7, 8, 9, 11} : Set ℕ) ∪ (squares)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 128, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 300, 340, 346, 349, 356, 422, 426, 439, 487, 499, 508, 516, 520, 534, 538, 542, 548, 674, 688}) ∪ cubes) ⊆ Law1110.spectrum := by
  apply Set.union_subset
  · apply Set.union_subset
    · exact Set.union_subset finite_1110 family_1110
    · rintro n ⟨hn, he⟩
      have hx : n ∉ E63.ExtendedBounds.remaining := by simpa only [dupont_exceptions_eq] using he
      exact ⟨hn, (DupontTwists.models (E63.ExtendedBounds.model hx)).2.2.1⟩
  · intro n hn; exact ⟨hn.1, (OpenConstructions.cubes_all hn).2.2.1⟩

theorem upper_1110 : Law1110.spectrum ⊆ positiveExcept {2, 3, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact not_two_1110 hn.2
  · exact NoteExclusion.not_three_1110 hn.2
  · exact (NegativeTransfer.route_1110_6).not_hasModel not_order_1110_6 hn.2

theorem cofinite_1110 : CofiniteSpectrum Law1110 := Pending.cofinite_1110

-- UNKNOWN: the exact spectrum of E1279 is not established in the note.
theorem finite_1279 : ({1, 5, 7, 8, 11} : Set ℕ) ⊆ Law1279.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1279.hasModel_one⟩
  · exact ⟨by decide, model_1279_5⟩
  · exact ⟨by decide, model_1279_7⟩
  · exact ⟨by decide, NoteWitness.model_1279_8⟩
  · exact ⟨by decide, model_1279_11⟩

theorem lower_1279 : ((({1, 5, 7, 8, 11} : Set ℕ)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 128, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 300, 340, 346, 349, 356, 422, 426, 439, 487, 499, 508, 516, 520, 534, 538, 542, 548, 674, 688}) ∪ cubes) ⊆ Law1279.spectrum := by
  apply Set.union_subset
  · apply Set.union_subset
    · exact finite_1279
    · rintro n ⟨hn, he⟩
      have hx : n ∉ E63.ExtendedBounds.remaining := by simpa only [dupont_exceptions_eq] using he
      exact ⟨hn, (DupontTwists.models (E63.ExtendedBounds.model hx)).2.2.2.1⟩
  · intro n hn; exact ⟨hn.1, (OpenConstructions.cubes_all hn).2.2.2.1⟩

theorem upper_1279 : Law1279.spectrum ⊆ positiveExcept {2, 3, 4, 6, 9, 13} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_two_1279 hn.2
  · exact NoteExclusion.not_three_1279 hn.2
  · exact (NegativeTransfer.route_1279_4).not_hasModel not_order_1279_4 hn.2
  · exact (NegativeTransfer.route_1279_6).not_hasModel not_order_1279_6 hn.2
  · exact not_order_1279_9 hn.2
  · exact not_order_1279_13 hn.2

theorem cofinite_1279 : CofiniteSpectrum Law1279 := Pending.cofinite_1279

-- UNKNOWN: the exact spectrum of E1286 is not established in the note.
theorem finite_1286 : ({1, 7, 9, 11, 13, 17, 19, 23, 29, 31, 32, 37, 43, 47, 53, 59, 67, 71, 73, 79, 113, 218, 240, 1008, 1009, 1898, 1017083} : Set ℕ) ⊆ Law1286.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1286.hasModel_one⟩
  · exact ⟨by decide, model_1286_7⟩
  · exact ⟨by decide, OpenWitnesses.model_1286_9⟩
  · exact ⟨by decide, E1083E1286.model_1286_11⟩
  · exact ⟨by decide, model_1286_13⟩
  · exact ⟨by decide, E1083E1286.model_1286_17⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_19⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_23⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_29⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_31⟩
  · exact ⟨by decide, E1083E1286.BinarySeed.model32⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_37⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_43⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_47⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_53⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_59⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_67⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_71⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_73⟩
  · exact ⟨by decide, E1083E1286.PrimeSeeds.model_1286_79⟩
  · exact ⟨by decide, E1083E1286.model_1286_113⟩
  · exact ⟨by decide, E1083E1286.BinarySeed.model218⟩
  · exact ⟨by decide, E1083E1286.BinaryHalves.model240⟩
  · exact ⟨by decide, E1083E1286.model_1286_1008⟩
  · exact ⟨by decide, E1083E1286.model_1286_1009⟩
  · exact ⟨by decide, E1083E1286.model_1286_1898⟩
  · exact ⟨by decide, E1083E1286.model_1286_1017083⟩

theorem family_1286 : (fourthPowers ∪ commonPointFourthOrders ∪ binaryPointFourthOrders ∪ designPairOrders) ⊆ Law1286.spectrum := by
  exact E1083E1286.family1286

theorem lower_1286 : (({1, 7, 9, 11, 13, 17, 19, 23, 29, 31, 32, 37, 43, 47, 53, 59, 67, 71, 73, 79, 113, 218, 240, 1008, 1009, 1898, 1017083} : Set ℕ) ∪ (fourthPowers ∪ commonPointFourthOrders ∪ binaryPointFourthOrders ∪ designPairOrders)) ⊆ Law1286.spectrum :=
  Set.union_subset finite_1286 family_1286

theorem upper_1286 : Law1286.spectrum ⊆ positiveExcept {2, 3, 4, 5, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_1286 hn.2
  · exact NoteExclusion.not_three_1286 hn.2
  · exact (NegativeTransfer.route_1286_4).not_hasModel not_order_1286_4 hn.2
  · exact (NegativeTransfer.route_1286_5).not_hasModel not_order_1286_5 hn.2
  · exact (NegativeTransfer.route_1286_6).not_hasModel not_order_1286_6 hn.2

theorem cofinite_1286 : CofiniteSpectrum Law1286 := Pending.cofinite_1286

-- UNKNOWN: the exact spectrum of E1313 is not established in the note.
theorem finite_1313 : ({1, 5, 7, 9, 13, 16, 17, 19, 23, 25, 31, 43, 47, 53, 59, 67, 71, 73, 79, 80, 81} : Set ℕ) ⊆ Law1313.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1313.hasModel_one⟩
  · exact ⟨by decide, model_1313_5⟩
  · exact ⟨by decide, model_1313_7⟩
  · exact ⟨by decide, SmallPairs.model_1313_9⟩
  · exact ⟨by decide, QuarticTail.small_1313_13⟩
  · exact ⟨by decide, QuarticTail.small_1313_16⟩
  · exact ⟨by decide, QuarticTail.small_1313_17⟩
  · exact ⟨by decide, OpenWitnesses.model_1313_19⟩
  · exact ⟨by decide, QuarticTail.small_1313_23⟩
  · exact ⟨by decide, QuarticTail.small_1313_25⟩
  · exact ⟨by decide, QuarticTail.small_1313_31⟩
  · exact ⟨by decide, QuarticTail.small_1313_43⟩
  · exact ⟨by decide, QuarticTail.small_1313_47⟩
  · exact ⟨by decide, QuarticTail.small_1313_53⟩
  · exact ⟨by decide, QuarticTail.small_1313_59⟩
  · exact ⟨by decide, QuarticTail.small_1313_67⟩
  · exact ⟨by decide, QuarticTail.small_1313_71⟩
  · exact ⟨by decide, QuarticTail.small_1313_73⟩
  · exact ⟨by decide, QuarticTail.small_1313_79⟩
  · exact ⟨by decide, QuarticTail.small_1313_80⟩
  · exact ⟨by decide, QuarticTail.small_1313_81⟩

theorem family_1313 : (fourthPowers) ⊆ Law1313.spectrum := by
  exact OpenConstructions.fourth_1313

theorem lower_1313 : ((({1, 5, 7, 9, 13, 16, 17, 19, 23, 25, 31, 43, 47, 53, 59, 67, 71, 73, 79, 80, 81} : Set ℕ) ∪ (fourthPowers)) ∪ quarticTailSeeds ∪ Set.Ici 107773) ⊆ Law1313.spectrum :=
  Set.union_subset (Set.union_subset (Set.union_subset finite_1313 family_1313) QuarticTail.finite_1313) (fun n hn => ⟨Nat.lt_of_lt_of_le (by decide : 0 < 107773) hn, QuarticTail.model_1313 n hn⟩)

theorem upper_1313 : Law1313.spectrum ⊆ positiveExcept {2, 3, 4, 6, 8, 11} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_two_1313 hn.2
  · exact NoteExclusion.not_three_1313 hn.2
  · exact (NegativeTransfer.route_1313_4).not_hasModel not_order_1313_4 hn.2
  · exact (NegativeTransfer.route_1313_6).not_hasModel not_order_1313_6 hn.2
  · exact not_order_1313_8 hn.2
  · exact not_order_1313_11 hn.2

theorem cofinite_1313 : CofiniteSpectrum Law1313 := Pending.cofinite_1313

-- Historical note bounds; the exact spectrum of E1480 is now proved.
theorem finite_1480 : ({1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} : Set ℕ) ⊆ Law1480.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1480.hasModel_one⟩
  · exact ⟨by decide, square_1480 2⟩
  · exact ⟨by decide, NoteWitness.model_1480_5⟩
  · exact ⟨by decide, NoteWitness.model_1480_6⟩
  · exact ⟨by decide, NoteWitness.model_1480_7⟩
  · exact ⟨by decide, NoteWitness.model_1480_8⟩
  · exact ⟨by decide, square_1480 3⟩
  · exact ⟨by decide, NoteWitness.model_1480_10⟩
  · exact ⟨by decide, models_1480 (by decide) (by decide)⟩
  · exact ⟨by decide, models_1480 (by decide) (by decide)⟩
  · exact ⟨by decide, models_1480 (by decide) (by decide)⟩
  · exact ⟨by decide, models_1480 (by decide) (by decide)⟩
  · exact ⟨by decide, models_1480 (by decide) (by decide)⟩
  · exact ⟨by decide, square_1480 4⟩
  · exact ⟨by decide, models_1480 (by decide) (by decide)⟩
  · exact ⟨by decide, models_1480 (by decide) (by decide)⟩

theorem family_1480 : (squares) ⊆ Law1480.spectrum := by
  rintro n ⟨hn, k, rfl⟩
  exact ⟨hn, square_1480 k⟩

theorem lower_1480 : (({1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} : Set ℕ) ∪ (squares)) ⊆ Law1480.spectrum :=
  Set.union_subset finite_1480 family_1480

theorem upper_1480 : Law1480.spectrum ⊆ positiveExcept {2, 3} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact not_two_1480 hn.2
  · exact not_order_1480_3 hn.2

-- UNKNOWN: the exact spectrum of E1483 is not established in the note.
theorem finite_1483 : ({1, 2, 4, 8, 9} : Set ℕ) ⊆ Law1483.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1483.hasModel_one⟩
  · exact ⟨by decide, two_1483⟩
  · exact ⟨by decide, square_1483 2⟩
  · exact ⟨by decide, NoteWitness.model_1483_8⟩
  · exact ⟨by decide, square_1483 3⟩

theorem family_1483 : (squares ∪ twiceSquares) ⊆ Law1483.spectrum := by
  rintro n (⟨hn, k, rfl⟩ | ⟨hn, k, rfl⟩)
  · exact ⟨hn, square_1483 k⟩
  · exact ⟨hn, two_1483.mul (square_1483 k)⟩

theorem lower_1483 : (({1, 2, 4, 8, 9} : Set ℕ) ∪ (squares ∪ twiceSquares)) ⊆ Law1483.spectrum :=
  Set.union_subset finite_1483 family_1483

theorem upper_1483 : Law1483.spectrum ⊆ positiveExcept {3, 5, 6, 7, 10, 11} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_three_1483 hn.2
  · exact (NegativeTransfer.route_1483_5).not_hasModel not_order_1483_5 hn.2
  · exact (NegativeTransfer.route_1483_6).not_hasModel not_order_1483_6 hn.2
  · exact not_order_1483_7 hn.2
  · exact not_order_1483_10 hn.2
  · exact not_order_1483_11 hn.2

-- Historical note bounds; the exact spectrum of E1485 is now proved.
theorem finite_1485 : ({1} : Set ℕ) ⊆ Law1485.spectrum := by
  intro n hn
  simp only [Set.mem_singleton_iff] at hn
  subst n
  exact ⟨by decide, Law1485.hasModel_one⟩

theorem family_1485 : (squares ∪ twiceSquares) ⊆ Law1485.spectrum := by
  rintro n (⟨hn, k, rfl⟩ | ⟨hn, k, rfl⟩)
  · exact ⟨hn, square_1485 k⟩
  · exact ⟨hn, twice_square_1485 k⟩

theorem lower_1485 : (({1} : Set ℕ) ∪ (squares ∪ twiceSquares)) ⊆ Law1485.spectrum :=
  Set.union_subset finite_1485 family_1485

theorem upper_1485 : Law1485.spectrum ⊆ positiveExcept {3, 11, 13} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact not_three_1485 hn.2
  · exact (NegativeTransfer.route_1485_11).not_hasModel not_order_1485_11 hn.2
  · exact (NegativeTransfer.route_1485_13).not_hasModel not_order_1485_13 hn.2

-- UNKNOWN: the exact spectrum of E1486 is not established in the note.
theorem finite_1486 : ({1, 11, 13, 21} : Set ℕ) ⊆ Law1486.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1486.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_1486_11⟩
  · exact ⟨by decide, NoteWitness.model_1486_13⟩
  · exact ⟨by decide, NoteWitness.model_1486_21⟩

theorem family_1486 : (squares ∪ shiftedSquares) ⊆ Law1486.spectrum := by
  apply Set.union_subset
  · rintro n ⟨hn, k, rfl⟩
    exact ⟨hn, square_1486 k⟩
  · exact Pending.shifted_squares_1486

theorem lower_1486 : (positiveExcept {2, 3, 5, 6, 7, 8, 10, 12, 14, 15, 17, 26}) ⊆ Law1486.spectrum :=
  E1486.lower_spectrum

theorem upper_1486 : Law1486.spectrum ⊆ positiveExcept {2, 3, 5, 6, 7, 8} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl
  · exact not_two_1486 hn.2
  · exact NoteExclusion.not_three_1486 hn.2
  · exact not_order_1486_5 hn.2
  · exact not_order_1486_6 hn.2
  · exact not_order_1486_7 hn.2
  · exact not_order_1486_8 hn.2

theorem cofinite_1486 : CofiniteSpectrum Law1486 := Pending.cofinite_1486

-- Historical note bounds; the exact spectrum of E1489 is now proved.
theorem finite_1489 : ({1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Set ℕ) ⊆ Law1489.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1489.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_1489_3⟩
  · exact ⟨by decide, model_1489_5⟩
  · exact ⟨by decide, NoteWitness.model_1489_6⟩
  · exact ⟨by decide, model_1489_7⟩
  · exact ⟨by decide, NoteWitness.model_1489_8⟩
  · exact ⟨by decide, NoteWitness.model_1489_9⟩
  · exact ⟨by decide, NoteWitness.model_1489_10⟩
  · exact ⟨by decide, model_1489_11⟩
  · exact ⟨by decide, NoteWitness.model_1489_12⟩
  · exact ⟨by decide, model_1489_13⟩
  · exact ⟨by decide, NoteWitness.model_1489_14⟩
  · exact ⟨by decide, NoteWitness.model_1489_15⟩
  · exact ⟨by decide, NoteWitness.model_1489_16⟩
  · exact ⟨by decide, NoteWitness.model_1489_17⟩
  · exact ⟨by decide, NoteWitness.model_1489_18⟩
  · exact ⟨by decide, NoteWitness.model_1489_19⟩
  · exact ⟨by decide, NoteWitness.model_1489_20⟩
  · exact ⟨by decide, NoteWitness.model_1489_21⟩

theorem lower_1489 : (({1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Set ℕ)) ⊆ Law1489.spectrum := finite_1489

theorem upper_1489 : Law1489.spectrum ⊆ positiveExcept {2, 4} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact not_two_1489 hn.2
  · exact (NegativeTransfer.route_1489_4).not_hasModel not_order_1489_4 hn.2

theorem cofinite_1489 : CofiniteSpectrum Law1489 := Pending.cofinite_1489

-- UNKNOWN: the exact spectrum of E1516 is not established in the note.
theorem finite_1516 : ({1, 5, 7, 8, 9, 11, 13, 16} : Set ℕ) ⊆ Law1516.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1516.hasModel_one⟩
  · exact ⟨by decide, model_1516_5⟩
  · exact ⟨by decide, model_1516_7⟩
  · exact ⟨by decide, NoteWitness.model_1516_8⟩
  · exact ⟨by decide, OpenWitnesses.model_1516_9⟩
  · exact ⟨by decide, model_1516_11⟩
  · exact ⟨by decide, model_1516_13⟩
  · exact ⟨by decide, E1516.model16⟩

theorem family_1516 : (fourthPowers) ⊆ Law1516.spectrum := by
  exact E1516.fourth_powers
theorem lower_1516 : ((({1, 5, 7, 8, 9, 11, 13, 16} : Set ℕ) ∪ (fourthPowers)) ∪ (positiveExcept {2, 3, 4, 6, 9, 10, 12, 13, 14, 15, 16, 18, 20, 22, 24, 26, 28, 30, 34, 38, 39, 42, 44, 46, 47, 48, 51, 52, 58, 60, 62, 65, 66, 68, 70, 71, 72, 73, 74, 75, 76, 80, 86, 87, 90, 91, 92, 94, 96, 98, 99, 100, 102, 104, 106, 108, 110, 112, 114, 116, 118, 122, 128, 132, 139, 142, 143, 146, 151, 153, 154, 158, 159, 163, 164, 170, 174, 179, 188, 195, 202, 207, 219, 233, 254, 258, 262, 268, 272, 300, 340, 346, 349, 356, 422, 426, 439, 487, 499, 508, 516, 520, 534, 538, 542, 548, 674, 688}) ∪ cubes) ⊆ Law1516.spectrum := by
  apply Set.union_subset
  · apply Set.union_subset
    · exact Set.union_subset finite_1516 family_1516
    · rintro n ⟨hn, he⟩
      have hx : n ∉ E63.ExtendedBounds.remaining := by simpa only [dupont_exceptions_eq] using he
      exact ⟨hn, (DupontTwists.models (E63.ExtendedBounds.model hx)).2.2.2.2⟩
  · intro n hn; exact ⟨hn.1, (OpenConstructions.cubes_all hn).2.2.2.2⟩

theorem upper_1516 : Law1516.spectrum ⊆ positiveExcept {2, 3, 4, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_two_1516 hn.2
  · exact NoteExclusion.not_three_1516 hn.2
  · exact (NegativeTransfer.route_1516_4).not_hasModel not_order_1516_4 hn.2
  · exact (NegativeTransfer.route_1516_6).not_hasModel not_order_1516_6 hn.2

theorem cofinite_1516 : CofiniteSpectrum Law1516 := Pending.cofinite_1516

-- Historical note bounds; the exact spectrum of E1719 is now proved.
theorem finite_1719 : ({1, 5, 6, 8} : Set ℕ) ⊆ Law1719.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1719.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_1719_5⟩
  · exact ⟨by decide, NoteWitness.model_1719_6⟩
  · exact ⟨by decide, NoteWitness.model_1719_8⟩

theorem family_1719 : (residues 3 {0, 1} ∅) ⊆ Law1719.spectrum := by
  intro n hn
  by_cases he : n = 6
  · subst n; exact ⟨by decide, NoteWitness.model_1719_6⟩
  · apply Pending.mendelsohn_1719
    exact ⟨hn.1, hn.2.1, by simpa using he⟩

theorem lower_1719 : (({1, 5, 6, 8} : Set ℕ) ∪ (residues 3 {0, 1} ∅)) ⊆ Law1719.spectrum :=
  Set.union_subset finite_1719 family_1719

theorem upper_1719 : Law1719.spectrum ⊆ positiveExcept {2} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_singleton] at he
  subst n
  exact not_two_1719 hn.2

-- UNKNOWN exact spectrum; transferred from E63.
theorem lower_73 : (positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}) ⊆ Law73.spectrum := by
  rw [spectrum_63_eq_73.symm]
  exact lower_63

theorem upper_73 : Law73.spectrum ⊆ positiveExcept {2, 6, 10, 14} := by
  rw [spectrum_63_eq_73.symm]
  exact upper_63

theorem cofinite_73 : CofiniteSpectrum Law73 := by
  unfold CofiniteSpectrum
  rw [spectrum_63_eq_73.symm]
  exact cofinite_63

-- UNKNOWN exact spectrum; transferred from E63.
theorem lower_118 : (positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}) ⊆ Law118.spectrum := by
  rw [(spectrum_63_eq_73.trans spectrum_73_eq_118).symm]
  exact lower_63

theorem upper_118 : Law118.spectrum ⊆ positiveExcept {2, 6, 10, 14} := by
  rw [(spectrum_63_eq_73.trans spectrum_73_eq_118).symm]
  exact upper_63

theorem cofinite_118 : CofiniteSpectrum Law118 := by
  unfold CofiniteSpectrum
  rw [(spectrum_63_eq_73.trans spectrum_73_eq_118).symm]
  exact cofinite_63

-- UNKNOWN exact spectrum; transferred from E63.
theorem lower_125 : (positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}) ⊆ Law125.spectrum := by
  rw [spectrum_63_eq_125.symm]
  exact lower_63

theorem upper_125 : Law125.spectrum ⊆ positiveExcept {2, 6, 10, 14} := by
  rw [spectrum_63_eq_125.symm]
  exact upper_63

theorem cofinite_125 : CofiniteSpectrum Law125 := by
  unfold CofiniteSpectrum
  rw [spectrum_63_eq_125.symm]
  exact cofinite_63

-- UNKNOWN exact spectrum; transferred from E63.
theorem lower_1692 : (positiveExcept {2, 6, 10, 14, 18, 26, 30, 38, 42, 90, 158}) ⊆ Law1692.spectrum := by
  rw [spectrum_63_eq_1692.symm]
  exact lower_63

theorem upper_1692 : Law1692.spectrum ⊆ positiveExcept {2, 6, 10, 14} := by
  rw [spectrum_63_eq_1692.symm]
  exact upper_63

theorem cofinite_1692 : CofiniteSpectrum Law1692 := by
  unfold CofiniteSpectrum
  rw [spectrum_63_eq_1692.symm]
  exact cofinite_63

-- UNKNOWN exact spectrum; transferred from E883.
theorem lower_1323 : (positiveExcept {3, 6, 9, 12, 15, 18, 24, 30, 39, 48, 51, 60, 75, 87, 96, 99, 102, 153, 159, 174, 195, 207, 219}) ⊆ Law1323.spectrum := by
  rw [spectrum_883_eq_1323.symm]
  exact lower_883

theorem upper_1323 : Law1323.spectrum ⊆ positiveExcept {3, 6, 9} := by
  rw [spectrum_883_eq_1323.symm]
  exact upper_883

theorem cofinite_1323 : CofiniteSpectrum Law1323 := by
  unfold CofiniteSpectrum
  rw [spectrum_883_eq_1323.symm]
  exact cofinite_883

-- UNKNOWN exact spectrum; transferred from E883.
theorem lower_1526 : (positiveExcept {3, 6, 9, 12, 15, 18, 24, 30, 39, 48, 51, 60, 75, 87, 96, 99, 102, 153, 159, 174, 195, 207, 219}) ⊆ Law1526.spectrum := by
  rw [spectrum_883_eq_1526.symm]
  exact lower_883

theorem upper_1526 : Law1526.spectrum ⊆ positiveExcept {3, 6, 9} := by
  rw [spectrum_883_eq_1526.symm]
  exact upper_883

theorem cofinite_1526 : CofiniteSpectrum Law1526 := by
  unfold CofiniteSpectrum
  rw [spectrum_883_eq_1526.symm]
  exact cofinite_883

end Spectrum.Note
