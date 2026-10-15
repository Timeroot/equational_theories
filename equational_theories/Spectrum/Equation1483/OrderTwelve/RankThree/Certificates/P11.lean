import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- CNF SHA-256: 52a7c99f86e91d15c4e3ef812c877d41b3dad4518939f2c7399d0f2881fd5d59.
Compact payload SHA-256: 82ff0d9d9b69e720fad37df949ebaa4502f1253372976c710fc6d3729c52bf48. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.OrderTwelve.RankThree.Certificates.P11
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../../data/spectrum/1483_order12_rank3_rup/P11.rup.xz")
  (branch [13, 25])
@[spectrum_native]
theorem checked : check refutation (branch [13, 25]) = true := by native_decide
theorem unsat : (branch [13, 25]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1483.OrderTwelve.RankThree.Certificates.P11
