import equational_theories.Spectrum.Equation883Nine.Predicates

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

namespace Spectrum.E883Nine

/-- First-row cycle lengths: [4, 5]. -/
@[spectrum_native]
theorem refuteRow48 (b c d e f g h i : BitVec 36)
    (hl : testLatin 19451413281 b c d e f g h i) : ¬ testLaw 19451413281 b c d e f g h i := by
  unfold testLatin testLaw op clip at *
  bv_decide (config := { timeout := 60, embeddedConstraintSubst := false })
spectrum_assert refuteRow48 complete

end Spectrum.E883Nine
