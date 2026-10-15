import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 7b927fa2444affa8fc8d7f8b6c39ccd1a70503cf41296ef680e7529e39cf441c.
Compact payload SHA-256 d1b1d62731634862d0b5c9da5fbac40725f26f3f031ca01d51111462b39610e6. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.C5G234
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/C5G234.rup.xz")
  (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [2,3,4])
@[spectrum_native]
theorem checked : check refutation (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [2,3,4]) = true := by native_decide
theorem unsat : (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [2,3,4]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.C5G234
