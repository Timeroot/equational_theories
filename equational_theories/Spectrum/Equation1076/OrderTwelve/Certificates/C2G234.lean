import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 bbeb251e00187ce1c46af6593c08eff70d22f1406fd31839dd6dab206f0560a7.
Compact payload SHA-256 faaacaa09f0520def71b8e61316ee2096d51a0511551501c3ab9b8ab328b3d7d. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.C2G234
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/C2G234.rup.xz")
  (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 2)) false [2,3,4])
@[spectrum_native]
theorem checked : check refutation (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 2)) false [2,3,4]) = true := by native_decide
theorem unsat : (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 2)) false [2,3,4]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.C2G234
