import equational_theories.Spectrum.Equation907Eight.Predicates

set_option maxHeartbeats 16000000
set_option maxRecDepth 32768

namespace Spectrum.E907Eight

@[spectrum_native]
theorem refuteRow02 (b c d e f g h : BitVec 24)
    (hl : testLatin 14473424 b c d e f g h) : ¬ testLaw 14473424 b c d e f g h := by
  unfold testLatin testLaw op at *
  bv_decide (config := { timeout := 120, embeddedConstraintSubst := false })
spectrum_assert refuteRow02 complete

end Spectrum.E907Eight
