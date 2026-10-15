import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 65d8baa28d46ed7fd40c934664bbe516ed978995862877f26b598e5a9f1e20e9.
Compact payload SHA-256 a5652c5304e57ec4af831bdcd0531c9daf88c26dc3e623fa3d8e379b6f5d2f39. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.C0
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/C0.rup.xz")
  (PointEncoding.natFormula (CanonicalData.row (CanonicalData.representative 0)) false)
@[spectrum_native]
theorem checked : check refutation (PointEncoding.natFormula (CanonicalData.row (CanonicalData.representative 0)) false) = true := by native_decide
theorem unsat : (PointEncoding.natFormula (CanonicalData.row (CanonicalData.representative 0)) false).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.C0
