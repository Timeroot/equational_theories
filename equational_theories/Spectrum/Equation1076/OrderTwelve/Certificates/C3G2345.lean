import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 ae325e3ec9c2e0fb03a2b63c0f05a2021110484050a5406c81b61b77608b2f75.
Compact payload SHA-256 a2ac9579033912e367c9dcda1fc23fbc3e9462b6cad3aa8bf22470a536834965. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.C3G2345
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/C3G2345.rup.xz")
  (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 3)) true [2,3,4,5])
@[spectrum_native]
theorem checked : check refutation (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 3)) true [2,3,4,5]) = true := by native_decide
theorem unsat : (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 3)) true [2,3,4,5]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.C3G2345
