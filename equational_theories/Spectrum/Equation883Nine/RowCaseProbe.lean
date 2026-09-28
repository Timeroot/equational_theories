import equational_theories.Spectrum.Equation883Nine.Predicates
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
namespace Spectrum.E883Nine
@[spectrum_native]
theorem probe (b c d e f g h i : BitVec 36) (hl : testLatin 32302645536 b c d e f g h i) : ¬ testLaw 32302645536 b c d e f g h i := by
  unfold testLatin testLaw op clip at *
  bv_decide (config := { timeout := 60, embeddedConstraintSubst := false })
end Spectrum.E883Nine
