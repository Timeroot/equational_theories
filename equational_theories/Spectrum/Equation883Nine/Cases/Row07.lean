import equational_theories.Spectrum.Equation883Nine.Predicates

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

namespace Spectrum.E883Nine

/-- First-row cycle lengths: [1, 4, 4]. -/
@[spectrum_native]
theorem refuteRow07 (b c d e f g h i : BitVec 36)
    (hl : testLatin 23746134816 b c d e f g h i) : ¬ testLaw 23746134816 b c d e f g h i := by
  unfold testLatin testLaw op clip at *
  bv_decide (config := { timeout := 60, embeddedConstraintSubst := false })
spectrum_assert refuteRow07 complete

end Spectrum.E883Nine
