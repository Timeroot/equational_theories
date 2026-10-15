import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 cf6f3aa2cc48c07c51144769fc158b41182a3b1fc0f0fa0e926635080d7db068.
Compact payload SHA-256 be72837e8a3422c2fe79d9a40281467cd15498a807c5c51923eab36815e6808f. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.C5G891011
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/C5G891011.rup.xz")
  (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [8,9,10,11])
@[spectrum_native]
theorem checked : check refutation (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [8,9,10,11]) = true := by native_decide
theorem unsat : (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 5)) true [8,9,10,11]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.C5G891011
