import equational_theories.Spectrum.Equation667EightClassification.Encoding
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

namespace Spectrum.E667.EightClassification
open Std.Sat Std.Tactic.BVDecide LRAT
private def proof : Array IntAction :=
  (parseLRATProof (include_gzip_str
    "../../../data/spectrum/667_eight_classification.lrat.gz").toUTF8).toOption.getD #[]
@[spectrum_native]
theorem checked : check proof natFormula = true := by native_decide

theorem unsat : natFormula.Unsat := check_sound proof _ checked

/-- The only idempotent-free eight-element model, up to relabelling. -/
theorem exists_iso [Magma K] (h : Equation667 K) (hf : ∀ x : K, x ◇ x ≠ x) :
    ∃ e : K ≃ K, ∀ x y, e (x ◇ y) = Eight.quotient (e x) (e y) :=
  classification unsat _ (fun x y => (h x y).symm) hf

/-- Squaring exchanges four pairs in an idempotent-free eight-point model. -/
theorem square_involutive [Magma K] (h : Equation667 K)
    (hf : ∀ x : K, x ◇ x ≠ x) (x : K) : (x ◇ x) ◇ (x ◇ x) = x := by
  obtain ⟨e,he⟩ := exists_iso h hf
  apply e.injective
  rw [he, he]
  exact (by decide +kernel : ∀ z : K,
    Eight.quotient (Eight.quotient z z) (Eight.quotient z z) = z) (e x)

/-- The unique idempotent-free eight-point model is medial. -/
theorem medial [Magma K] (h : Equation667 K) (hf : ∀ x : K, x ◇ x ≠ x)
    (a b c d : K) : (a ◇ b) ◇ (c ◇ d) = (a ◇ c) ◇ (b ◇ d) := by
  obtain ⟨e,he⟩ := exists_iso h hf
  apply e.injective
  simp only [he]
  exact (by decide +kernel : ∀ a b c d : K,
    Eight.quotient (Eight.quotient a b) (Eight.quotient c d) =
      Eight.quotient (Eight.quotient a c) (Eight.quotient b d)) (e a) (e b) (e c) (e d)

spectrum_assert exists_iso complete
spectrum_assert square_involutive complete
spectrum_assert medial complete
end Spectrum.E667.EightClassification
