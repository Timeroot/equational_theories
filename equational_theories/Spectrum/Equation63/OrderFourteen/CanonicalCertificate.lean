import equational_theories.Spectrum.Equation63.OrderFourteen.RowTransfer
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Only 21 cycle types need refutations; CanonicalData proves the relabelings
of all 70 ordered rows. The final small refutation checks row coverage. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E63.OrderFourteen.CanonicalCertificate
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData RowTransfer CanonicalData

private def data : Array ByteArray := #[
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case01.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case22.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case19.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case17.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case26.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case16.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case14.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case18.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case21.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case27.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case44.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case65.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case62.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case33.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case36.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case46.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case45.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case48.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case66.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case60.rup.xz",
  include_binary_xz "../../../../data/spectrum/63_fourteen_rup/case69.rup.xz"]
private def caseProof (j : Fin 21) : Array IntAction :=
  CompactRup.reconstruct data[j.val]! (rowFormula (row (representative j)))

@[spectrum_native]
theorem checked_cases : (List.finRange 21).all (fun j =>
    check (caseProof j) (rowFormula (row (representative j)))) = true := by native_decide

theorem case_unsat (j : Fin 21) : (rowFormula (row (representative j))).Unsat :=
  check_sound _ _ (List.all_eq_true.mp checked_cases j (List.mem_finRange _))

private def coverageProof : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../data/spectrum/63_fourteen_rup/coverage.rup.xz") coverage

@[spectrum_native]
theorem checked_coverage : check coverageProof coverage = true := by native_decide

theorem coverage_unsat : coverage.Unsat := check_sound _ _ checked_coverage

spectrum_assert case_unsat complete
spectrum_assert coverage_unsat complete
end Spectrum.E63.OrderFourteen.CanonicalCertificate
