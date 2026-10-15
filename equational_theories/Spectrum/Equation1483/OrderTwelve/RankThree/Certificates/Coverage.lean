import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- CNF SHA-256: 04c8364909e958f23a2d9e3a3320e68a003668863821e1170494e548fa9442ee.
Compact payload SHA-256: 65acbd7a6f8f4de59fe5f3a322b2d4852b00be3bd7b6a27f7d516eb880fc5bc7. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.OrderTwelve.RankThree.Certificates.Coverage
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../../data/spectrum/1483_order12_rank3_rup/Coverage.rup.xz")
  (coverage)
@[spectrum_native]
theorem checked : check refutation (coverage) = true := by native_decide
theorem unsat : (coverage).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1483.OrderTwelve.RankThree.Certificates.Coverage
