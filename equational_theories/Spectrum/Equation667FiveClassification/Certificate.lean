import equational_theories.Spectrum.Equation667FiveClassification.Encoding
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

namespace Spectrum.E667.FiveClassification
open Std.Sat Std.Tactic.BVDecide LRAT
private def proof : Array IntAction :=
  (parseLRATProof (include_gzip_str
    "../../../data/spectrum/667_five_classification.lrat.gz").toUTF8).toOption.getD #[]
@[spectrum_native]
theorem checked : check proof natFormula = true := by native_decide

theorem unsat : natFormula.Unsat := check_sound proof _ checked

/-- The only idempotent-free five-element model, up to relabelling. -/
theorem exists_iso [Magma K] (h : Equation667 K) (hf : ∀ x : K, x ◇ x ≠ x) :
    ∃ e : K ≃ K, ∀ x y, e (x ◇ y) = FiberThree.quotient (e x) (e y) :=
  classification unsat _ (fun x y => (h x y).symm) hf

spectrum_assert exists_iso complete
end Spectrum.E667.FiveClassification
