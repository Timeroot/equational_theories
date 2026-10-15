import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- CNF SHA-256: c8c4a62f6bb30708e05e7193bf62b2b679ec3fcdc1e9ba1a80f0fbaf77fee8c4.
Compact payload SHA-256: 1a816353de9b4ac4277030346d2f4c280fa76058e74b29204496ea7ba239cba8. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.OrderTwelve.RankThree.Certificates.P21
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../../data/spectrum/1483_order12_rank3_rup/P21.rup.xz")
  (branch [14, 25])
@[spectrum_native]
theorem checked : check refutation (branch [14, 25]) = true := by native_decide
theorem unsat : (branch [14, 25]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1483.OrderTwelve.RankThree.Certificates.P21
