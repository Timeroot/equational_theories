import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Encoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- CNF SHA-256: 15950f6f7396b54746552fce39f09e121c991848b5bb60352146e85c88852a86.
Compact payload SHA-256: 0aeff3fefa007cdec74870401f00abbf3d5357ba4ee95b8470c59eed5826d72b. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1483.OrderTwelve.RankThree.Certificates.P13
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../../data/spectrum/1483_order12_rank3_rup/P13.rup.xz")
  (branch [13, 27])
@[spectrum_native]
theorem checked : check refutation (branch [13, 27]) = true := by native_decide
theorem unsat : (branch [13, 27]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1483.OrderTwelve.RankThree.Certificates.P13
