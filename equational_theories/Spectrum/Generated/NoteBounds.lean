import equational_theories.Spectrum.Note
import equational_theories.Spectrum.Generated
import equational_theories.Spectrum.Generated.NoteWitnesses
import equational_theories.Spectrum.Generated.NoteObligations
import equational_theories.Spectrum.Generated.NoteExclusions

/-! Every lower bound, initial segment, and undisputed cofinite claim of §3.
UNKNOWN exact spectra are intentionally represented by bounds, not equalities.
Some statements depend on the explicitly named Pending obligations. -/

open Law Law.MagmaLaw
namespace Spectrum.Note

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
  · exact ⟨by decide, NoteWitness.model_63_9⟩
  · exact ⟨by decide, model_63_11⟩
  · exact ⟨by decide, NoteWitness.model_63_12⟩
  · exact ⟨by decide, model_63_13⟩

theorem lower_63 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law63.spectrum := finite_63

theorem upper_63 : Law63.spectrum ⊆ positiveExcept {2, 6, 10} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact not_two_63 hn.2
  · exact Pending.not_order_63_6 hn.2
  · exact Pending.not_order_63_10 hn.2

theorem cofinite_63 : CofiniteSpectrum Law63 := Pending.cofinite_63

-- UNKNOWN: the exact spectrum of E115 is not established in the note.
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
  · exact Pending.not_order_115_6 hn.2

-- UNKNOWN: the exact spectrum of E467 is not established in the note.
theorem finite_467 : ({1, 5, 7, 8} : Set ℕ) ⊆ Law467.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law467.hasModel_one⟩
  · exact ⟨by decide, model_467_5⟩
  · exact ⟨by decide, model_467_7⟩
  · exact ⟨by decide, NoteWitness.model_467_8⟩

theorem family_467 : (oddSumTwoSquares) ⊆ Law467.spectrum := by
  exact Pending.odd_sums_467

theorem lower_467 : (({1, 5, 7, 8} : Set ℕ) ∪ (oddSumTwoSquares)) ⊆ Law467.spectrum :=
  Set.union_subset finite_467 family_467

theorem upper_467 : Law467.spectrum ⊆ positiveExcept {2, 3, 4, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_two_467 hn.2
  · exact NoteExclusion.not_three_467 hn.2
  · exact Pending.not_order_467_4 hn.2
  · exact Pending.not_order_467_6 hn.2

theorem cofinite_467 : CofiniteSpectrum Law467 := Pending.cofinite_467

-- UNKNOWN: the exact spectrum of E481 is not established in the note.
theorem finite_481 : ({1, 7, 9, 12} : Set ℕ) ⊆ Law481.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law481.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_481_7⟩
  · exact ⟨by decide, NoteWitness.model_481_9⟩
  · exact ⟨by decide, Pending.model_481_12⟩

theorem family_481 : (residues 3 {1, 2} {7}) ⊆ Law481.spectrum := by
  exact Pending.loops_481

theorem lower_481 : (({1, 7, 9, 12} : Set ℕ) ∪ (residues 3 {1, 2} {7})) ⊆ Law481.spectrum :=
  Set.union_subset finite_481 family_481

theorem upper_481 : Law481.spectrum ⊆ positiveExcept {3, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact not_three_481 hn.2
  · exact Pending.not_order_481_6 hn.2

-- UNKNOWN: the exact spectrum of E501 is not established in the note.
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
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  subst n
  exact not_two_501 hn.2

-- UNKNOWN: the exact spectrum of E667 is not established in the note.
theorem finite_667 : ({1, 7, 9} : Set ℕ) ⊆ Law667.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl
  · exact ⟨by decide, Law667.hasModel_one⟩
  · exact ⟨by decide, model_667_7⟩
  · exact ⟨by decide, NoteWitness.model_667_9⟩

theorem family_667 : (residues 3 {1, 2} ∅) ⊆ Law667.spectrum := by
  intro n hn
  by_cases he : n = 7
  · subst n; exact ⟨by decide, model_667_7⟩
  · apply Pending.loops_667
    exact ⟨hn.1, hn.2.1, by simpa using he⟩

theorem lower_667 : (({1, 7, 9} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law667.spectrum :=
  Set.union_subset finite_667 family_667

theorem upper_667 : Law667.spectrum ⊆ positiveExcept {3} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  subst n
  exact not_three_667 hn.2

-- UNKNOWN: the exact spectrum of E670 is not established in the note.
theorem finite_670 : ({1, 4, 5} : Set ℕ) ⊆ Law670.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl
  · exact ⟨by decide, Law670.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_670_4⟩
  · exact ⟨by decide, model_670_5⟩

theorem lower_670 : (({1, 4, 5} : Set ℕ)) ⊆ Law670.spectrum := finite_670

theorem upper_670 : Law670.spectrum ⊆ positiveExcept {2, 3, 6, 7} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_two_670 hn.2
  · exact NoteExclusion.not_three_670 hn.2
  · exact Pending.not_order_670_6 hn.2
  · exact Pending.not_order_670_7 hn.2

theorem cofinite_670 : CofiniteSpectrum Law670 := Pending.cofinite_670

-- UNKNOWN: the exact spectrum of E677 is not established in the note.
theorem finite_677 : ({1, 5, 7, 9, 11, 13, 16} : Set ℕ) ⊆ Law677.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law677.hasModel_one⟩
  · exact ⟨by decide, model_677_5⟩
  · exact ⟨by decide, model_677_7⟩
  · exact ⟨by decide, NoteWitness.model_677_9⟩
  · exact ⟨by decide, model_677_11⟩
  · exact ⟨by decide, model_677_13⟩
  · exact ⟨by decide, NoteWitness.model_677_16⟩

theorem lower_677 : (({1, 5, 7, 9, 11, 13, 16} : Set ℕ)) ⊆ Law677.spectrum := finite_677

theorem upper_677 : Law677.spectrum ⊆ positiveExcept {2} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  subst n
  exact not_two_677 hn.2

theorem cofinite_677 : CofiniteSpectrum Law677 := Pending.cofinite_677

-- UNKNOWN: the exact spectrum of E704 is not established in the note.
theorem finite_704 : ({1, 5, 7, 8} : Set ℕ) ⊆ Law704.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law704.hasModel_one⟩
  · exact ⟨by decide, model_704_5⟩
  · exact ⟨by decide, model_704_7⟩
  · exact ⟨by decide, NoteWitness.model_704_8⟩

theorem lower_704 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law704.spectrum := finite_704

theorem upper_704 : Law704.spectrum ⊆ positiveExcept {2, 3, 4, 6, 9} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_704 hn.2
  · exact NoteExclusion.not_three_704 hn.2
  · exact Pending.not_order_704_4 hn.2
  · exact Pending.not_order_704_6 hn.2
  · exact Pending.not_order_704_9 hn.2

theorem cofinite_704 : CofiniteSpectrum Law704 := Pending.cofinite_704

-- UNKNOWN: the exact spectrum of E873 is not established in the note.
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
  · exact Pending.not_order_873_6 hn.2

-- UNKNOWN: the exact spectrum of E883 is not established in the note.
theorem finite_883 : ({1, 7} : Set ℕ) ⊆ Law883.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl
  · exact ⟨by decide, Law883.hasModel_one⟩
  · exact ⟨by decide, model_883_7⟩

theorem family_883 : (residues 3 {1, 2} ∅) ⊆ Law883.spectrum := by
  intro n hn
  by_cases he : n = 7
  · subst n; exact ⟨by decide, model_883_7⟩
  · apply Pending.loops_883
    exact ⟨hn.1, hn.2.1, by simpa using he⟩

theorem lower_883 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law883.spectrum :=
  Set.union_subset finite_883 family_883

theorem upper_883 : Law883.spectrum ⊆ positiveExcept {3} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  subst n
  exact not_three_883 hn.2

theorem cofinite_883 : CofiniteSpectrum Law883 := Pending.cofinite_883

-- UNKNOWN: the exact spectrum of E907 is not established in the note.
theorem finite_907 : ({1, 3, 7, 9, 13} : Set ℕ) ⊆ Law907.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law907.hasModel_one⟩
  · exact ⟨by decide, model_907_3⟩
  · exact ⟨by decide, model_907_7⟩
  · exact ⟨by decide, model_907_9⟩
  · exact ⟨by decide, model_907_13⟩

theorem lower_907 : (({1, 3, 7, 9, 13} : Set ℕ)) ⊆ Law907.spectrum := finite_907

theorem upper_907 : Law907.spectrum ⊆ positiveExcept {2, 4, 5, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_two_907 hn.2
  · exact Pending.not_order_907_4 hn.2
  · exact Pending.not_order_907_5 hn.2
  · exact Pending.not_order_907_6 hn.2

-- UNKNOWN: the exact spectrum of E1076 is not established in the note.
theorem finite_1076 : ({1, 5} : Set ℕ) ⊆ Law1076.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl
  · exact ⟨by decide, Law1076.hasModel_one⟩
  · exact ⟨by decide, model_1076_5⟩

theorem lower_1076 : (({1, 5} : Set ℕ)) ⊆ Law1076.spectrum := finite_1076

theorem upper_1076 : Law1076.spectrum ⊆ positiveExcept {2, 3, 4, 6, 7} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_1076 hn.2
  · exact NoteExclusion.not_three_1076 hn.2
  · exact Pending.not_order_1076_4 hn.2
  · exact Pending.not_order_1076_6 hn.2
  · exact Pending.not_order_1076_7 hn.2

theorem cofinite_1076 : CofiniteSpectrum Law1076 := Pending.cofinite_1076

-- UNKNOWN: the exact spectrum of E1083 is not established in the note.
theorem finite_1083 : ({1, 3, 4, 7, 8, 9} : Set ℕ) ⊆ Law1083.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1083.hasModel_one⟩
  · exact ⟨by decide, model_1083_3⟩
  · exact ⟨by decide, NoteWitness.model_1083_4⟩
  · exact ⟨by decide, model_1083_7⟩
  · exact ⟨by decide, NoteWitness.model_1083_8⟩
  · exact ⟨by decide, model_1083_9⟩

theorem lower_1083 : (({1, 3, 4, 7, 8, 9} : Set ℕ)) ⊆ Law1083.spectrum := finite_1083

theorem upper_1083 : Law1083.spectrum ⊆ positiveExcept {2} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  subst n
  exact not_two_1083 hn.2

-- UNKNOWN: the exact spectrum of E1110 is not established in the note.
theorem finite_1110 : ({1, 4, 5, 7, 8, 9} : Set ℕ) ⊆ Law1110.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1110.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_1110_4⟩
  · exact ⟨by decide, model_1110_5⟩
  · exact ⟨by decide, model_1110_7⟩
  · exact ⟨by decide, NoteWitness.model_1110_8⟩
  · exact ⟨by decide, NoteWitness.model_1110_9⟩

theorem lower_1110 : (({1, 4, 5, 7, 8, 9} : Set ℕ)) ⊆ Law1110.spectrum := finite_1110

theorem upper_1110 : Law1110.spectrum ⊆ positiveExcept {2, 3, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact not_two_1110 hn.2
  · exact NoteExclusion.not_three_1110 hn.2
  · exact Pending.not_order_1110_6 hn.2

theorem cofinite_1110 : CofiniteSpectrum Law1110 := Pending.cofinite_1110

-- UNKNOWN: the exact spectrum of E1279 is not established in the note.
theorem finite_1279 : ({1, 5, 7, 8} : Set ℕ) ⊆ Law1279.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1279.hasModel_one⟩
  · exact ⟨by decide, model_1279_5⟩
  · exact ⟨by decide, model_1279_7⟩
  · exact ⟨by decide, NoteWitness.model_1279_8⟩

theorem lower_1279 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law1279.spectrum := finite_1279

theorem upper_1279 : Law1279.spectrum ⊆ positiveExcept {2, 3, 4, 6, 9} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_1279 hn.2
  · exact NoteExclusion.not_three_1279 hn.2
  · exact Pending.not_order_1279_4 hn.2
  · exact Pending.not_order_1279_6 hn.2
  · exact Pending.not_order_1279_9 hn.2

theorem cofinite_1279 : CofiniteSpectrum Law1279 := Pending.cofinite_1279

-- UNKNOWN: the exact spectrum of E1286 is not established in the note.
theorem finite_1286 : ({1, 7} : Set ℕ) ⊆ Law1286.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl
  · exact ⟨by decide, Law1286.hasModel_one⟩
  · exact ⟨by decide, model_1286_7⟩

theorem lower_1286 : (({1, 7} : Set ℕ)) ⊆ Law1286.spectrum := finite_1286

theorem upper_1286 : Law1286.spectrum ⊆ positiveExcept {2, 3, 4, 5, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact not_two_1286 hn.2
  · exact NoteExclusion.not_three_1286 hn.2
  · exact Pending.not_order_1286_4 hn.2
  · exact Pending.not_order_1286_5 hn.2
  · exact Pending.not_order_1286_6 hn.2

-- UNKNOWN: the exact spectrum of E1313 is not established in the note.
theorem finite_1313 : ({1, 5, 7} : Set ℕ) ⊆ Law1313.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl
  · exact ⟨by decide, Law1313.hasModel_one⟩
  · exact ⟨by decide, model_1313_5⟩
  · exact ⟨by decide, model_1313_7⟩

theorem lower_1313 : (({1, 5, 7} : Set ℕ)) ⊆ Law1313.spectrum := finite_1313

theorem upper_1313 : Law1313.spectrum ⊆ positiveExcept {2, 3, 4, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_two_1313 hn.2
  · exact NoteExclusion.not_three_1313 hn.2
  · exact Pending.not_order_1313_4 hn.2
  · exact Pending.not_order_1313_6 hn.2

-- UNKNOWN: the exact spectrum of E1480 is not established in the note.
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
  · exact ⟨by decide, Pending.model_1480_10⟩
  · exact ⟨by decide, Pending.model_1480_11⟩
  · exact ⟨by decide, Pending.model_1480_12⟩
  · exact ⟨by decide, Pending.model_1480_13⟩
  · exact ⟨by decide, Pending.model_1480_14⟩
  · exact ⟨by decide, Pending.model_1480_15⟩
  · exact ⟨by decide, square_1480 4⟩
  · exact ⟨by decide, Pending.model_1480_17⟩
  · exact ⟨by decide, Pending.model_1480_18⟩

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

theorem family_1483 : (squares) ⊆ Law1483.spectrum := by
  rintro n ⟨hn, k, rfl⟩
  exact ⟨hn, square_1483 k⟩

theorem lower_1483 : (({1, 2, 4, 8, 9} : Set ℕ) ∪ (squares)) ⊆ Law1483.spectrum :=
  Set.union_subset finite_1483 family_1483

theorem upper_1483 : Law1483.spectrum ⊆ positiveExcept {3, 5, 6, 7} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_three_1483 hn.2
  · exact Pending.not_order_1483_5 hn.2
  · exact Pending.not_order_1483_6 hn.2
  · exact Pending.not_order_1483_7 hn.2

-- UNKNOWN: the exact spectrum of E1485 is not established in the note.
theorem finite_1485 : ({1} : Set ℕ) ⊆ Law1485.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  subst n
  exact ⟨by decide, Law1485.hasModel_one⟩

theorem family_1485 : (squares ∪ twiceSquares) ⊆ Law1485.spectrum := by
  rintro n (⟨hn, k, rfl⟩ | ⟨hn, k, rfl⟩)
  · exact ⟨hn, square_1485 k⟩
  · exact ⟨hn, twice_square_1485 k⟩

theorem lower_1485 : (({1} : Set ℕ) ∪ (squares ∪ twiceSquares)) ⊆ Law1485.spectrum :=
  Set.union_subset finite_1485 family_1485

theorem upper_1485 : Law1485.spectrum ⊆ positiveExcept {3} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  subst n
  exact not_three_1485 hn.2

-- UNKNOWN: the exact spectrum of E1486 is not established in the note.
theorem finite_1486 : ({1, 13, 21} : Set ℕ) ⊆ Law1486.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl
  · exact ⟨by decide, Law1486.hasModel_one⟩
  · exact ⟨by decide, Pending.model_1486_13⟩
  · exact ⟨by decide, Pending.model_1486_21⟩

theorem family_1486 : (squares ∪ shiftedSquares) ⊆ Law1486.spectrum := by
  apply Set.union_subset
  · rintro n ⟨hn, k, rfl⟩
    exact ⟨hn, square_1486 k⟩
  · exact Pending.shifted_squares_1486

theorem lower_1486 : (({1, 13, 21} : Set ℕ) ∪ (squares ∪ shiftedSquares)) ⊆ Law1486.spectrum :=
  Set.union_subset finite_1486 family_1486

theorem upper_1486 : Law1486.spectrum ⊆ positiveExcept {2} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  subst n
  exact not_two_1486 hn.2

-- UNKNOWN: the exact spectrum of E1489 is not established in the note.
theorem finite_1489 : ({1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Set ℕ) ⊆ Law1489.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1489.hasModel_one⟩
  · exact ⟨by decide, NoteWitness.model_1489_3⟩
  · exact ⟨by decide, model_1489_5⟩
  · exact ⟨by decide, Pending.model_1489_6⟩
  · exact ⟨by decide, model_1489_7⟩
  · exact ⟨by decide, NoteWitness.model_1489_8⟩
  · exact ⟨by decide, NoteWitness.model_1489_9⟩
  · exact ⟨by decide, Pending.model_1489_10⟩
  · exact ⟨by decide, model_1489_11⟩
  · exact ⟨by decide, Pending.model_1489_12⟩
  · exact ⟨by decide, model_1489_13⟩
  · exact ⟨by decide, Pending.model_1489_14⟩
  · exact ⟨by decide, NoteWitness.model_1489_15⟩
  · exact ⟨by decide, NoteWitness.model_1489_16⟩
  · exact ⟨by decide, NoteWitness.model_1489_17⟩
  · exact ⟨by decide, Pending.model_1489_18⟩
  · exact ⟨by decide, NoteWitness.model_1489_19⟩
  · exact ⟨by decide, Pending.model_1489_20⟩
  · exact ⟨by decide, NoteWitness.model_1489_21⟩

theorem lower_1489 : (({1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Set ℕ)) ⊆ Law1489.spectrum := finite_1489

theorem upper_1489 : Law1489.spectrum ⊆ positiveExcept {2, 4} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact not_two_1489 hn.2
  · exact Pending.not_order_1489_4 hn.2

theorem cofinite_1489 : CofiniteSpectrum Law1489 := Pending.cofinite_1489

-- UNKNOWN: the exact spectrum of E1516 is not established in the note.
theorem finite_1516 : ({1, 5, 7, 8} : Set ℕ) ⊆ Law1516.spectrum := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨by decide, Law1516.hasModel_one⟩
  · exact ⟨by decide, model_1516_5⟩
  · exact ⟨by decide, model_1516_7⟩
  · exact ⟨by decide, NoteWitness.model_1516_8⟩

theorem lower_1516 : (({1, 5, 7, 8} : Set ℕ)) ⊆ Law1516.spectrum := finite_1516

theorem upper_1516 : Law1516.spectrum ⊆ positiveExcept {2, 3, 4, 6} := by
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact not_two_1516 hn.2
  · exact NoteExclusion.not_three_1516 hn.2
  · exact Pending.not_order_1516_4 hn.2
  · exact Pending.not_order_1516_6 hn.2

theorem cofinite_1516 : CofiniteSpectrum Law1516 := Pending.cofinite_1516

-- UNKNOWN: the exact spectrum of E1719 is not established in the note.
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
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  subst n
  exact not_two_1719 hn.2

-- UNKNOWN exact spectrum; transferred from E63.
theorem lower_73 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law73.spectrum := by
  rw [spectrum_63_eq_73.symm]
  exact lower_63

theorem upper_73 : Law73.spectrum ⊆ positiveExcept {2, 6, 10} := by
  rw [spectrum_63_eq_73.symm]
  exact upper_63

theorem cofinite_73 : CofiniteSpectrum Law73 := by
  unfold CofiniteSpectrum
  rw [spectrum_63_eq_73.symm]
  exact cofinite_63

-- UNKNOWN exact spectrum; transferred from E63.
theorem lower_118 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law118.spectrum := by
  rw [(spectrum_63_eq_73.trans spectrum_73_eq_118).symm]
  exact lower_63

theorem upper_118 : Law118.spectrum ⊆ positiveExcept {2, 6, 10} := by
  rw [(spectrum_63_eq_73.trans spectrum_73_eq_118).symm]
  exact upper_63

theorem cofinite_118 : CofiniteSpectrum Law118 := by
  unfold CofiniteSpectrum
  rw [(spectrum_63_eq_73.trans spectrum_73_eq_118).symm]
  exact cofinite_63

-- UNKNOWN exact spectrum; transferred from E63.
theorem lower_125 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law125.spectrum := by
  rw [spectrum_63_eq_125.symm]
  exact lower_63

theorem upper_125 : Law125.spectrum ⊆ positiveExcept {2, 6, 10} := by
  rw [spectrum_63_eq_125.symm]
  exact upper_63

theorem cofinite_125 : CofiniteSpectrum Law125 := by
  unfold CofiniteSpectrum
  rw [spectrum_63_eq_125.symm]
  exact cofinite_63

-- UNKNOWN exact spectrum; transferred from E63.
theorem lower_1692 : (({1, 3, 4, 5, 7, 8, 9, 11, 12, 13} : Set ℕ)) ⊆ Law1692.spectrum := by
  rw [spectrum_63_eq_1692.symm]
  exact lower_63

theorem upper_1692 : Law1692.spectrum ⊆ positiveExcept {2, 6, 10} := by
  rw [spectrum_63_eq_1692.symm]
  exact upper_63

theorem cofinite_1692 : CofiniteSpectrum Law1692 := by
  unfold CofiniteSpectrum
  rw [spectrum_63_eq_1692.symm]
  exact cofinite_63

-- UNKNOWN exact spectrum; transferred from E115.
theorem lower_880 : (({1, 5} : Set ℕ) ∪ (residues 3 {0, 1} {6})) ⊆ Law880.spectrum := by
  rw [spectrum_115_eq_880.symm]
  exact lower_115

theorem upper_880 : Law880.spectrum ⊆ positiveExcept {2, 6} := by
  rw [spectrum_115_eq_880.symm]
  exact upper_115

-- UNKNOWN exact spectrum; transferred from E481.
theorem lower_1496 : (({1, 7, 9, 12} : Set ℕ) ∪ (residues 3 {1, 2} {7})) ⊆ Law1496.spectrum := by
  rw [spectrum_481_eq_1496.symm]
  exact lower_481

theorem upper_1496 : Law1496.spectrum ⊆ positiveExcept {3, 6} := by
  rw [spectrum_481_eq_1496.symm]
  exact upper_481

-- UNKNOWN exact spectrum; transferred from E883.
theorem lower_1323 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law1323.spectrum := by
  rw [spectrum_883_eq_1323.symm]
  exact lower_883

theorem upper_1323 : Law1323.spectrum ⊆ positiveExcept {3} := by
  rw [spectrum_883_eq_1323.symm]
  exact upper_883

theorem cofinite_1323 : CofiniteSpectrum Law1323 := by
  unfold CofiniteSpectrum
  rw [spectrum_883_eq_1323.symm]
  exact cofinite_883

-- UNKNOWN exact spectrum; transferred from E883.
theorem lower_1526 : (({1, 7} : Set ℕ) ∪ (residues 3 {1, 2} ∅)) ⊆ Law1526.spectrum := by
  rw [spectrum_883_eq_1526.symm]
  exact lower_883

theorem upper_1526 : Law1526.spectrum ⊆ positiveExcept {3} := by
  rw [spectrum_883_eq_1526.symm]
  exact upper_883

theorem cofinite_1526 : CofiniteSpectrum Law1526 := by
  unfold CofiniteSpectrum
  rw [spectrum_883_eq_1526.symm]
  exact cofinite_883

end Spectrum.Note
