import equational_theories.Spectrum.Equation907Eight.Predicates

set_option maxHeartbeats 16000000
set_option maxRecDepth 32768

namespace Spectrum.E907Eight

@[spectrum_native]
theorem refuteRow12 (b c d e f g h : BitVec 24)
    (hl : testLatin 16431184 b c d e f g h) : ¬ testLaw 16431184 b c d e f g h := by
  unfold testLatin testLaw op at *
  bv_decide (config := { timeout := 120, embeddedConstraintSubst := false })
spectrum_assert refuteRow12 complete

end Spectrum.E907Eight
