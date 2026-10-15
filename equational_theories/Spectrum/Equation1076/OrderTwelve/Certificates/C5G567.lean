import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 b72f8f8304e9e20000d4890c64f1f13dd573c32e40fd4ef85aa022f686852404.
Compact payload SHA-256 71807ce1b444d01784ca5534c45b4dd8c1dcd9d61966926ef7d9a2bf9842c7e4. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.C5G567
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/C5G567.rup.xz")
  (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [5,6,7])
@[spectrum_native]
theorem checked : check refutation (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [5,6,7]) = true := by native_decide
theorem unsat : (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [5,6,7]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.C5G567
