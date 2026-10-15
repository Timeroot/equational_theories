import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- CNF SHA-256: 99557b56f2fcb944121cd8641092c679b6e2a4dfb02b2f0d999f975075958054.
Compact payload SHA-256: 042f1e86c3adf5cfb58e7b96bde4e0bf611e0b56c447928dc1a0eee6d040d96b. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.OrderTwelve.RankThree.Certificates.P12
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../../data/spectrum/1483_order12_rank3_rup/P12.rup.xz")
  (branch [13, 26])
@[spectrum_native]
theorem checked : check refutation (branch [13, 26]) = true := by native_decide
theorem unsat : (branch [13, 26]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1483.OrderTwelve.RankThree.Certificates.P12
