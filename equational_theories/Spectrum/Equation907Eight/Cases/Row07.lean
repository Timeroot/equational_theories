import equational_theories.Spectrum.Equation907Eight.Predicates

set_option maxHeartbeats 16000000
set_option maxRecDepth 32768

namespace Spectrum.E907Eight

@[spectrum_native]
theorem refuteRow07 (b c d e f g h : BitVec 24)
    (hl : testLatin 15946448 b c d e f g h) : ¬ testLaw 15946448 b c d e f g h := by
  unfold testLatin testLaw op at *
  bv_decide (config := { timeout := 120, embeddedConstraintSubst := false })
spectrum_assert refuteRow07 complete

end Spectrum.E907Eight
