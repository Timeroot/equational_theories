import equational_theories.Spectrum.Shapes
import equational_theories.Spectrum.Status
import equational_theories.Equations.All

/-!
# Explicit outstanding proof obligations from the spectrum note

These are claims made in the note, NOT its question-marked conjectures.
Each declaration distinguishes `proofAvailable` (an outlined/external proof
awaiting Lean) from `noteGap` (a missing mathematical step not yet reconstructed).
A citation or reported ATP run is not a locally available proof certificate. They currently use `sorry`. Keeping them in this module separates
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
spectrum_pending models_66 proofAvailable "§3.4.1–2"
  "Use established Mendelsohn design existence; idempotent semisymmetric models satisfy E66. Formalize the external design theorem and substitution."

/-- §3.4.2: necessity of the Mendelsohn congruence and the exceptional order 6. -/
theorem orders_66 {n : ℕ} (h : n ∈ Law66.spectrum) : n ∈ residues 3 {0, 1} {6} := by
  sorry
spectrum_pending orders_66 proofAvailable "§3.4.2"
  "Twist by S(x)=x*x, count directed triples, and exclude order 6. The note sketches the reduction to standard design obstructions."

/-- §3.7: construct a square root of swapping unequal ordered pairs. -/
theorem models_167 {n : ℕ} (h : n ∈ residues 4 {0, 1} ∅) : Law167.HasModel n := by
  sorry
spectrum_pending models_167 proofAvailable "§3.7"
  "Pair unordered off-diagonal pairs and make four-cycles squaring to swap; choose diagonal fixed points. The finite construction is explicit."

/-- §3.7: the permutation on unequal ordered pairs has four-element orbits. -/
theorem orders_167 {n : ℕ} (h : n ∈ Law167.spectrum) : n ∈ residues 4 {0, 1} ∅ := by
  sorry
spectrum_pending orders_167 proofAvailable "§3.7"
  "The map (x,y) to (x*y,y*x) has four-cycles off the diagonal. Count n(n-1) modulo 4."

/-- §3.7: Knuth's cardinality theorem for finite central groupoids. -/
theorem orders_168 {n : ℕ} (h : n ∈ Law168.spectrum) : n ∈ squares := by
  sorry
spectrum_pending orders_168 proofAvailable "§3.7; cited theorem of Knuth"
  "External established square-cardinality theorem for finite central groupoids. The note cites the theorem rather than reproducing its proof; a Lean version is needed."

/-- §3.3: the Gaussian-integer quotient by `(k + l*i)` has order `k²+l²`. -/
theorem models_546 {n : ℕ} (h : n ∈ sumTwoSquares) : Law546.HasModel n := by
  sorry
spectrum_pending models_546 proofAvailable "§3.3"
  "Use Z[i]/(k+li) with operation -x+i*y; verify the identity and quotient cardinality k²+l²."

/-- §3.3: the Gaussian-module structure forces even valuations at primes 3 mod 4. -/
theorem orders_546 {n : ℕ} (h : n ∈ Law546.spectrum) : n ∈ sumTwoSquares := by
  sorry
spectrum_pending orders_546 noteGap "§3.3, 'with some more work'"
  "The affine Gaussian-module representation of an arbitrary E546 magma is asserted without derivation. The prime-valuation argument is sketched, but this representation step has not been reconstructed."

/-- §3.4.1,4: adjoining an identity to a Mendelsohn quasigroup. -/
theorem models_887 {n : ℕ} (h : n ∈ residues 3 {1, 2} {7}) : Law887.HasModel n := by
  sorry
spectrum_pending models_887 proofAvailable "§3.4.1,4"
  "Adjoin an identity to a Mendelsohn quasigroup of order n-1; formalize design existence and the explicit extension."

/-- §3.4.4: remove the identity of a semisymmetric loop. -/
theorem orders_887 {n : ℕ} (h : n ∈ Law887.spectrum) : n ∈ residues 3 {1, 2} {7} := by
  sorry
spectrum_pending orders_887 proofAvailable "§3.4.4"
  "Remove the identity of the semisymmetric loop and apply the standard Mendelsohn counting obstruction and exceptional order 6."

/-- §3.3: a finite Boolean group has power-of-two cardinality. -/
theorem orders_895 {n : ℕ} (h : n ∈ Law895.spectrum) : n ∈ powersTwo := by
  sorry
spectrum_pending orders_895 proofAvailable "§3.3"
  "E895 characterizes Boolean groups. Reconstruct the group and use the standard power-of-two cardinality theorem for finite elementary abelian 2-groups."

/-- §3.3: the parameterized Boolean-group operation defined from E898. -/
theorem orders_898 {n : ℕ} (h : n ∈ Law898.spectrum) : n ∈ powersTwo := by
  sorry
spectrum_pending orders_898 noteGap "§3.3, 'we work out'"
  "The operation ((u*x)*(y*u))*u is asserted to satisfy E895. The derivation from E898 is omitted and has not been reconstructed here."

/-- §3.6: the indicated odd Gaussian-quotient models of the twisted Dupont law. -/
theorem odd_sums_467 : oddSumTwoSquares ⊆ Law467.spectrum := by
  sorry
spectrum_pending odd_sums_467 proofAvailable "§3.6"
  "Verify the displayed linear operation on an odd-order Gaussian quotient; formalize the quotient cardinality."

/-- §3.7: the additional `k²+2`, `k≥3`, central-groupoid specialization. -/
theorem shifted_squares_1486 : shiftedSquares ⊆ Law1486.spectrum := by
  sorry
spectrum_pending shifted_squares_1486 noteGap "§3.7; external discussion link"
  "The note reports k²+2 models without giving their construction. Recover the construction before attempting the general Lean proof."

/-- §3.4.5: E115 is obeyed by every Mendelsohn quasigroup. -/
theorem mendelsohn_115 : residues 3 {0, 1} {6} ⊆ Law115.spectrum := by
  sorry
spectrum_pending mendelsohn_115 proofAvailable "§3.4.5"
  "Idempotent semisymmetric quasigroups obey E115 by substitution; use Mendelsohn-system existence."

/-- §3.4.6: E481 is obeyed by every semisymmetric loop. -/
theorem loops_481 : residues 3 {1, 2} {7} ⊆ Law481.spectrum := by
  sorry
spectrum_pending loops_481 proofAvailable "§3.4.6"
  "Semisymmetric-loop neutral-element and unipotence identities give E481; use the loop spectrum."

/-- §3.4.7: E667 is obeyed by every semisymmetric loop. -/
theorem loops_667 : residues 3 {1, 2} {7} ⊆ Law667.spectrum := by
  sorry
spectrum_pending loops_667 proofAvailable "§3.4.7"
  "Substitute semisymmetric-loop identities into E667; use the loop spectrum."

/-- §3.4.7: E883 is obeyed by every semisymmetric loop. -/
theorem loops_883 : residues 3 {1, 2} {7} ⊆ Law883.spectrum := by
  sorry
spectrum_pending loops_883 proofAvailable "§3.4.7"
  "Substitute semisymmetric-loop identities into E883; use the loop spectrum."

/-- §3.4.7: E1719 is obeyed by every Mendelsohn quasigroup. -/
theorem mendelsohn_1719 : residues 3 {0, 1} {6} ⊆ Law1719.spectrum := by
  sorry
spectrum_pending mendelsohn_1719 proofAvailable "§3.4.7"
  "Idempotence reduces E1719 to semisymmetry; use Mendelsohn-system existence."

-- §3.5–6 and §3.8: Wilson mixed-block-design existence and gluing.
-- E1313 is deliberately absent: the note contradicts itself about cofiniteness.
theorem cofinite_63 : CofiniteSpectrum Law63 := by sorry
spectrum_pending cofinite_63 proofAvailable "§3.5–6; Wilson mixed-block-design theorem (1975)"
  "Glue idempotent Dupont models of orders 8 and 11 with Wilson's theorem; use the stated idempotent twists/parastrophy. Formalize the external theorem and gluing."
theorem cofinite_467 : CofiniteSpectrum Law467 := by sorry
spectrum_pending cofinite_467 proofAvailable "§3.5–6; Wilson mixed-block-design theorem (1975)"
  "Glue idempotent Dupont models of orders 8 and 11 with Wilson's theorem; use the stated idempotent twists/parastrophy. Formalize the external theorem and gluing."
theorem cofinite_670 : CofiniteSpectrum Law670 := by sorry
spectrum_pending cofinite_670 noteGap "§3.1 and §3.8 (E670); unfinished §3.5"
  "Cofiniteness is reported, but the needed idempotent models/block sizes or a reduction to Dupont gluing are not specified. No complete proof sketch has been recovered here."
theorem cofinite_677 : CofiniteSpectrum Law677 := by sorry
spectrum_pending cofinite_677 noteGap "§3.1 and §3.8 (E677); unfinished §3.5"
  "Cofiniteness is reported, but the needed idempotent models/block sizes or a reduction to Dupont gluing are not specified. No complete proof sketch has been recovered here."
theorem cofinite_704 : CofiniteSpectrum Law704 := by sorry
spectrum_pending cofinite_704 proofAvailable "§3.5–6; Wilson mixed-block-design theorem (1975)"
  "Glue idempotent Dupont models of orders 8 and 11 with Wilson's theorem; use the stated idempotent twists/parastrophy. Formalize the external theorem and gluing."
theorem cofinite_883 : CofiniteSpectrum Law883 := by sorry
spectrum_pending cofinite_883 proofAvailable "§3.5–6; Wilson mixed-block-design theorem (1975)"
  "Glue idempotent Dupont models of orders 8 and 11 with Wilson's theorem; use the stated idempotent twists/parastrophy. Formalize the external theorem and gluing."
theorem cofinite_1076 : CofiniteSpectrum Law1076 := by sorry
spectrum_pending cofinite_1076 noteGap "§3.1 and §3.8 (E1076); unfinished §3.5"
  "Cofiniteness is reported, but the needed idempotent models/block sizes or a reduction to Dupont gluing are not specified. No complete proof sketch has been recovered here."
theorem cofinite_1110 : CofiniteSpectrum Law1110 := by sorry
spectrum_pending cofinite_1110 proofAvailable "§3.5–6; Wilson mixed-block-design theorem (1975)"
  "Glue idempotent Dupont models of orders 8 and 11 with Wilson's theorem; use the stated idempotent twists/parastrophy. Formalize the external theorem and gluing."
theorem cofinite_1279 : CofiniteSpectrum Law1279 := by sorry
spectrum_pending cofinite_1279 proofAvailable "§3.5–6; Wilson mixed-block-design theorem (1975)"
  "Glue idempotent Dupont models of orders 8 and 11 with Wilson's theorem; use the stated idempotent twists/parastrophy. Formalize the external theorem and gluing."
theorem cofinite_1489 : CofiniteSpectrum Law1489 := by sorry
spectrum_pending cofinite_1489 noteGap "§3.1 and §3.8 (E1489); unfinished §3.5"
  "Cofiniteness is reported, but the needed idempotent models/block sizes or a reduction to Dupont gluing are not specified. No complete proof sketch has been recovered here."
theorem cofinite_1516 : CofiniteSpectrum Law1516 := by sorry
spectrum_pending cofinite_1516 proofAvailable "§3.5–6; Wilson mixed-block-design theorem (1975)"
  "Glue idempotent Dupont models of orders 8 and 11 with Wilson's theorem; use the stated idempotent twists/parastrophy. Formalize the external theorem and gluing."

end Spectrum.Pending
