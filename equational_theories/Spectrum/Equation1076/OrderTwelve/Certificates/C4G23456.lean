import equational_theories.Spectrum.Equation1076.OrderTwelve.PointEncoding
import equational_theories.Spectrum.Status
import SpectrumCertificateData

/- Generated data: CNF SHA-256 4e769bd210e326ccf19448168f3bd445b51f17e744342d28498675a256cdbfa2.
Compact payload SHA-256 282c9bfdd12d4dea7d974ad470a9b3fedf5d2df6d17ecbd16ca6868f819f0bc2. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace Spectrum.E1076.OrderTwelve.Certificates.C4G23456
open Std.Sat Std.Tactic.BVDecide LRAT Spectrum.CertificateData
private def refutation : Array IntAction := CompactRup.reconstruct
  (include_binary_xz "../../../../../data/spectrum/1076_order12_rup/C4G23456.rup.xz")
  (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 4)) true [2,3,4,5,6])
@[spectrum_native]
theorem checked : check refutation (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 4)) true [2,3,4,5,6]) = true := by native_decide
theorem unsat : (PointEncoding.groupFormula (CanonicalData.row (CanonicalData.representative 4)) true [2,3,4,5,6]).Unsat := check_sound refutation _ checked
spectrum_assert unsat complete
end Spectrum.E1076.OrderTwelve.Certificates.C4G23456
