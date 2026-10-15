import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- CNF SHA-256: 4627047f045bd39f3faa154e8eb20a8e9b53184f73ac6ed75236b4a8e5f2af40.
Compact payload SHA-256: 8c5f9119c2c838e96749acc80bb72f8c5dc1b56d09e8973e1e2d7f38ca4e9441. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.OrderTwelve.RankThree.Certificates.P222
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../../data/spectrum/1483_order12_rank3_rup/P222.rup.xz")
  (branch [14, 26, 38])
@[spectrum_native]
theorem checked : check refutation (branch [14, 26, 38]) = true := by native_decide
theorem unsat : (branch [14, 26, 38]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1483.OrderTwelve.RankThree.Certificates.P222
