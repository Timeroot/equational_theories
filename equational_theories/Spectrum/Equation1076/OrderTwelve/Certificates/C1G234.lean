import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 5ca925f25cf2d7cb5a6cffa202b6a7506dfe530155868f42c9153a23fcb2c6d3.
Compact payload SHA-256 950d79ae0253d9898122bd3cdd474b74e922868b218cfeec30f5e646fe094b14. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.C1G234
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/C1G234.rup.xz")
  (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 1)) false [2,3,4])
@[spectrum_native]
theorem checked : check refutation (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 1)) false [2,3,4]) = true := by native_decide
theorem unsat : (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 1)) false [2,3,4]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.C1G234
