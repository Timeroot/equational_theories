import equational_theories.Spectrum.Shapes
import equational_theories.Equations.All

/-!
# Explicit outstanding proof obligations from the spectrum note

These statements are established claims of the note, NOT its question-marked
conjectures. They currently use `sorry`. Keeping them in this module separates
complete specifications from completed formal proofs. In particular importing
the catalogue does not make these results axiom-free: its audit reports the
transitive dependency on `sorryAx`.

The finite certificates and constructions elsewhere do not depend on this file.
-/

open Law Law.MagmaLaw
namespace Spectrum.Pending

/-- §3.4.1–2: Mendelsohn triple-system existence and the involution twist. -/
theorem models_66 {n : ℕ} (h : n ∈ residues 3 {0, 1} {6}) : Law66.HasModel n := by
  sorry

/-- §3.4.2: necessity of the Mendelsohn congruence and the exceptional order 6. -/
theorem orders_66 {n : ℕ} (h : n ∈ Law66.spectrum) : n ∈ residues 3 {0, 1} {6} := by
  sorry

/-- §3.7: construct a square root of swapping unequal ordered pairs. -/
theorem models_167 {n : ℕ} (h : n ∈ residues 4 {0, 1} ∅) : Law167.HasModel n := by
  sorry

/-- §3.7: the permutation on unequal ordered pairs has four-element orbits. -/
theorem orders_167 {n : ℕ} (h : n ∈ Law167.spectrum) : n ∈ residues 4 {0, 1} ∅ := by
  sorry

/-- §3.7: Knuth's cardinality theorem for finite central groupoids. -/
theorem orders_168 {n : ℕ} (h : n ∈ Law168.spectrum) : n ∈ squares := by
  sorry

/-- §3.3: the Gaussian-integer quotient by `(k + l*i)` has order `k²+l²`. -/
theorem models_546 {n : ℕ} (h : n ∈ sumTwoSquares) : Law546.HasModel n := by
  sorry

/-- §3.3: the Gaussian-module structure forces even valuations at primes 3 mod 4. -/
theorem orders_546 {n : ℕ} (h : n ∈ Law546.spectrum) : n ∈ sumTwoSquares := by
  sorry

/-- §3.4.1,4: adjoining an identity to a Mendelsohn quasigroup. -/
theorem models_887 {n : ℕ} (h : n ∈ residues 3 {1, 2} {7}) : Law887.HasModel n := by
  sorry

/-- §3.4.4: remove the identity of a semisymmetric loop. -/
theorem orders_887 {n : ℕ} (h : n ∈ Law887.spectrum) : n ∈ residues 3 {1, 2} {7} := by
  sorry

/-- §3.3: a finite Boolean group has power-of-two cardinality. -/
theorem orders_895 {n : ℕ} (h : n ∈ Law895.spectrum) : n ∈ powersTwo := by
  sorry

/-- §3.3: the parameterized Boolean-group operation defined from E898. -/
theorem orders_898 {n : ℕ} (h : n ∈ Law898.spectrum) : n ∈ powersTwo := by
  sorry

/-- §3.6: the indicated odd Gaussian-quotient models of the twisted Dupont law. -/
theorem odd_sums_467 : oddSumTwoSquares ⊆ Law467.spectrum := by
  sorry

/-- §3.7: the additional `k²+2`, `k≥3`, central-groupoid specialization. -/
theorem shifted_squares_1486 : shiftedSquares ⊆ Law1486.spectrum := by
  sorry

/-- §3.4.5: E115 is obeyed by every Mendelsohn quasigroup. -/
theorem mendelsohn_115 : residues 3 {0, 1} {6} ⊆ Law115.spectrum := by
  sorry

/-- §3.4.6: E481 is obeyed by every semisymmetric loop. -/
theorem loops_481 : residues 3 {1, 2} {7} ⊆ Law481.spectrum := by
  sorry

/-- §3.4.7: E667 is obeyed by every semisymmetric loop. -/
theorem loops_667 : residues 3 {1, 2} {7} ⊆ Law667.spectrum := by
  sorry

/-- §3.4.7: E883 is obeyed by every semisymmetric loop. -/
theorem loops_883 : residues 3 {1, 2} {7} ⊆ Law883.spectrum := by
  sorry

/-- §3.4.7: E1719 is obeyed by every Mendelsohn quasigroup. -/
theorem mendelsohn_1719 : residues 3 {0, 1} {6} ⊆ Law1719.spectrum := by
  sorry

-- §3.5–6 and §3.8: Wilson mixed-block-design existence and gluing.
-- E1313 is deliberately absent: the note contradicts itself about cofiniteness.
theorem cofinite_63 : CofiniteSpectrum Law63 := by sorry
theorem cofinite_467 : CofiniteSpectrum Law467 := by sorry
theorem cofinite_670 : CofiniteSpectrum Law670 := by sorry
theorem cofinite_677 : CofiniteSpectrum Law677 := by sorry
theorem cofinite_704 : CofiniteSpectrum Law704 := by sorry
theorem cofinite_883 : CofiniteSpectrum Law883 := by sorry
theorem cofinite_1076 : CofiniteSpectrum Law1076 := by sorry
theorem cofinite_1110 : CofiniteSpectrum Law1110 := by sorry
theorem cofinite_1279 : CofiniteSpectrum Law1279 := by sorry
theorem cofinite_1489 : CofiniteSpectrum Law1489 := by sorry
theorem cofinite_1516 : CofiniteSpectrum Law1516 := by sorry

end Spectrum.Pending
