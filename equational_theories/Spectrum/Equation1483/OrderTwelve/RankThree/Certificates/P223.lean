import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- CNF SHA-256: 2a11c4d9803a1ed3602af536908649e23e12f5935370dae32b93371151918c87.
Compact payload SHA-256: 8e29b03239dc8da0677b3a9dd0ace1f65a2ab968a535c55288d4b9279299196f. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.OrderTwelve.RankThree.Certificates.P223
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../../data/spectrum/1483_order12_rank3_rup/P223.rup.xz")
  (branch [14, 26, 39])
@[spectrum_native]
theorem checked : check refutation (branch [14, 26, 39]) = true := by native_decide
theorem unsat : (branch [14, 26, 39]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1483.OrderTwelve.RankThree.Certificates.P223
