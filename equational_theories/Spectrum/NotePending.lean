import equational_theories.Spectrum.Shapes
import equational_theories.Spectrum.Status
import equational_theories.Spectrum.WeakCentralCardinality
import equational_theories.Spectrum.Equation66
import equational_theories.Spectrum.Equation546
import equational_theories.Spectrum.SemisymmetricLoop
import equational_theories.Spectrum.BooleanCardinality
import equational_theories.Spectrum.Equation167
import equational_theories.Spectrum.TwistedGaussian
import equational_theories.Spectrum.QuasigroupBounds
import equational_theories.Spectrum.Equation63
import equational_theories.Spectrum.Equation1489
import equational_theories.Spectrum.Equation667883FieldBounds
import equational_theories.Spectrum.Equation1486.FiniteBounds
import equational_theories.Spectrum.DupontTwists
import equational_theories.Spectrum.QuarticTail
import equational_theories.Spectrum.PBD.WilsonInstances
import equational_theories.Spectrum.Equation670.Cofiniteness
import equational_theories.Spectrum.Equation677.Cofiniteness
import equational_theories.Spectrum.Equation1083_1286.Cofiniteness
import equational_theories.Equations.All

/-!
# Explicit outstanding proof obligations from the spectrum note and research supplements

These are claims made in the note or linked research supplements, NOT the
note's question-marked conjectures.
Each declaration distinguishes `proofAvailable` (an outlined/external proof
awaiting Lean) from `noteGap` (a missing mathematical step not yet reconstructed).
A citation or reported ATP run is not a locally available proof certificate.
The outstanding declarations use `sorry`; completed proofs retain
compatibility names with `complete` assertions. Keeping the obligations here separates
complete specifications from completed formal proofs. In particular importing
the catalogue does not make these results axiom-free: its audit reports the
transitive dependency on `sorryAx`.

The finite certificates and constructions elsewhere do not depend on this file.
-/

open Law Law.MagmaLaw
namespace Spectrum.Pending

/-- §3.4.1–2, now proved by explicit idempotent Latin squares and Bose constructions. -/
theorem models_66 {n : ℕ} (h : n ∈ residues 3 {0, 1} {6}) : Law66.HasModel n :=
  Spectrum.models_66 h
spectrum_assert models_66 complete

/-- §3.4.2, now proved by the squaring twist, directed-pair count, and six-point certificate. -/
theorem orders_66 {n : ℕ} (h : n ∈ Law66.spectrum) : n ∈ residues 3 {0, 1} {6} :=
  Spectrum.orders_66 h
spectrum_assert orders_66 complete

/-- §3.7, now proved by pairing unordered pairs and rotating their four orientations. -/
theorem models_167 {n : ℕ} (h : n ∈ residues 4 {0, 1} ∅) : Law167.HasModel n :=
  Spectrum.models_167 h
spectrum_assert models_167 complete

/-- §3.7, now proved by the sign of coordinate swap on ordered pairs. -/
theorem orders_167 {n : ℕ} (h : n ∈ Law167.spectrum) : n ∈ residues 4 {0, 1} ∅ :=
  Spectrum.orders_167 h
spectrum_assert orders_167 complete

/-- §3.3, now proved using square models and modular square roots of minus one. -/
theorem models_546 {n : ℕ} (h : n ∈ sumTwoSquares) : Law546.HasModel n :=
  Spectrum.models_546 h
spectrum_assert models_546 complete

/-- §3.3, now proved by the affine Gaussian-module representation and Sylow parity. -/
theorem orders_546 {n : ℕ} (h : n ∈ Law546.spectrum) : n ∈ sumTwoSquares :=
  Spectrum.orders_546 h
spectrum_assert orders_546 complete

/-- §3.4.1,4, now proved by adjoining an identity to a Mendelsohn quasigroup. -/
theorem models_887 {n : ℕ} (h : n ∈ residues 3 {1, 2} {7}) : Law887.HasModel n :=
  Spectrum.models_887 h
spectrum_assert models_887 complete

/-- §3.4.4, now proved by removing the identity and applying the Mendelsohn obstructions. -/
theorem orders_887 {n : ℕ} (h : n ∈ Law887.spectrum) : n ∈ residues 3 {1, 2} {7} :=
  Spectrum.orders_887 h
spectrum_assert orders_887 complete

/-- §3.3, now proved by reconstructing a Boolean group and applying the p-group cardinality theorem. -/
theorem orders_895 {n : ℕ} (h : n ∈ Law895.spectrum) : n ∈ powersTwo :=
  Spectrum.orders_895 h
spectrum_assert orders_895 complete

/-- §3.3, now proved by the checked parameterized reduction to E895. -/
theorem orders_898 {n : ℕ} (h : n ∈ Law898.spectrum) : n ∈ powersTwo :=
  Spectrum.orders_898 h
spectrum_assert orders_898 complete

/-- §3.6: the indicated odd Gaussian-quotient models of the twisted Dupont law. -/
theorem odd_sums_467 : oddSumTwoSquares ⊆ Law467.spectrum := Spectrum.odd_sums_467
spectrum_assert odd_sums_467 complete

/-- §3.7, now covered by the explicit graph construction and finite bridges. -/
theorem shifted_squares_1486 : shiftedSquares ⊆ Law1486.spectrum := E1486.shifted_squares
spectrum_assert shifted_squares_1486 complete

/-- Compatibility name: the general prime-order theorem now proves this exclusion. -/
theorem not_order_1485_11 : ¬ Law1485.HasModel 11 := Spectrum.not_order_1485_11
spectrum_assert not_order_1485_11 complete

/-- Compatibility name: the general prime-order theorem now proves this exclusion. -/
theorem not_order_1485_13 : ¬ Law1485.HasModel 13 := Spectrum.not_order_1485_13
spectrum_assert not_order_1485_13 complete

/-- §3.4.5: E115 is obeyed by every Mendelsohn quasigroup. -/
theorem mendelsohn_115 : residues 3 {0, 1} {6} ⊆ Law115.spectrum := Spectrum.mendelsohn_115
spectrum_assert mendelsohn_115 complete

/-- §3.4.6: E481 is obeyed by every semisymmetric loop. -/
theorem loops_481 : residues 3 {1, 2} {7} ⊆ Law481.spectrum := Spectrum.loops_481
spectrum_assert loops_481 complete

/-- §3.4.7: E667 is obeyed by every semisymmetric loop. -/
theorem loops_667 : residues 3 {1, 2} {7} ⊆ Law667.spectrum := Spectrum.loops_667
spectrum_assert loops_667 complete

/-- §3.4.7: E883 is obeyed by every semisymmetric loop. -/
theorem loops_883 : residues 3 {1, 2} {7} ⊆ Law883.spectrum := Spectrum.loops_883
spectrum_assert loops_883 complete

/-- §3.4.7: E1719 is obeyed by every Mendelsohn quasigroup. -/
theorem mendelsohn_1719 : residues 3 {0, 1} {6} ⊆ Law1719.spectrum := Spectrum.mendelsohn_1719
spectrum_assert mendelsohn_1719 complete

-- §3.5–6 and §3.8: constructive cofinite bounds and remaining obligations.
-- E1076 and E1313 now use the explicit quartic construction certificate.
/-- Explicit constructive bound: every order at least 159. -/
theorem cofinite_63 : CofiniteSpectrum Law63 := E63.cofinite
spectrum_assert cofinite_63 complete
theorem cofinite_667 : CofiniteSpectrum Law667 := E667.FieldBounds.cofinite
spectrum_assert cofinite_667 complete
theorem cofinite_467 : CofiniteSpectrum Law467 := DupontTwists.cofinite_467
spectrum_assert cofinite_467 complete
/-- The idempotent seeds at 9, 11, and 16 and constructive design existence give a full tail. -/
theorem cofinite_670 : CofiniteSpectrum Law670 := E670.cofinite
spectrum_assert cofinite_670 complete

/-- The design-existence input for E677, proved by weighted designs and eventual periodicity. -/
theorem wilson_5_11_16 : PBD.WilsonExistence {5,11,16} := PBD.wilson_5_11_16
spectrum_assert wilson_5_11_16 complete

/-- The shared design-existence input for E1083/E1286, now fully proved. -/
theorem wilson_7_9_16 : PBD.WilsonExistence {7,9,16} := PBD.wilson_7_9_16
spectrum_assert wilson_7_9_16 complete

theorem cofinite_677 : CofiniteSpectrum Law677 := E677.cofinite_of_wilson wilson_5_11_16
spectrum_assert cofinite_677 complete
theorem cofinite_704 : CofiniteSpectrum Law704 := DupontTwists.cofinite_704
spectrum_assert cofinite_704 complete
theorem cofinite_883 : CofiniteSpectrum Law883 := E883.FieldBounds.cofinite
spectrum_assert cofinite_883 complete
theorem cofinite_1076 : CofiniteSpectrum Law1076 := QuarticTail.cofinite_1076
spectrum_assert cofinite_1076 complete
theorem cofinite_1083 : CofiniteSpectrum Law1083 :=
  E1083E1286.cofinite_of_wilson (which := false) wilson_7_9_16
spectrum_assert cofinite_1083 complete
theorem cofinite_1110 : CofiniteSpectrum Law1110 := DupontTwists.cofinite_1110
spectrum_assert cofinite_1110 complete
theorem cofinite_1279 : CofiniteSpectrum Law1279 := DupontTwists.cofinite_1279
spectrum_assert cofinite_1279 complete
theorem cofinite_1286 : CofiniteSpectrum Law1286 :=
  E1083E1286.cofinite_of_wilson (which := true) wilson_7_9_16
spectrum_assert cofinite_1286 complete
theorem cofinite_1313 : CofiniteSpectrum Law1313 := QuarticTail.cofinite_1313
spectrum_assert cofinite_1313 complete
theorem cofinite_1489 : CofiniteSpectrum Law1489 := by
  exact ⟨5, fun n hn => ⟨by omega, models_1489 (by omega) (by omega)⟩⟩
spectrum_assert cofinite_1489 complete
theorem cofinite_1486 : CofiniteSpectrum Law1486 := E1486.cofinite
spectrum_assert cofinite_1486 complete
theorem cofinite_1516 : CofiniteSpectrum Law1516 := DupontTwists.cofinite_1516
spectrum_assert cofinite_1516 complete

end Spectrum.Pending
