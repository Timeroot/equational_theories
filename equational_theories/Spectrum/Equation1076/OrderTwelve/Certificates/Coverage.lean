import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 3cdd476d43a4357b51eb3df0516a5d9c67c8a71af94c73ed7b33891f5ac850ed.
Compact payload SHA-256 421bfd17569b04282af2644e00134e529f1d8bcac63f79ea054cd861c8c5e521. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.Coverage
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/Coverage.rup.xz")
  (RowTransfer.coverage)
@[spectrum_native]
theorem checked : check refutation (RowTransfer.coverage) = true := by native_decide
theorem unsat : (RowTransfer.coverage).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.Coverage
