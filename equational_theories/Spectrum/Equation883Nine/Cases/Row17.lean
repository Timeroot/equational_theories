import equational_theories.Spectrum.Equation883Nine.RowCaseProbe

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

namespace Spectrum.E883Nine

/-- First-row cycle lengths: [1, 2, 2, 2, 2]. -/
theorem refuteRow17 (b c d e f g h i : BitVec 36)
    (hl : testLatin 32302645536 b c d e f g h i) : ¬ testLaw 32302645536 b c d e f g h i :=
  probe b c d e f g h i hl
spectrum_assert refuteRow17 complete

end Spectrum.E883Nine
