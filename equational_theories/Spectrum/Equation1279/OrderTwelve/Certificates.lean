import equational_theories.Spectrum.Equation1279.OrderTwelve.Batch0
import equational_theories.Spectrum.Equation1279.OrderTwelve.Batch1
import equational_theories.Spectrum.Equation1279.OrderTwelve.Batch2
import equational_theories.Spectrum.Equation1279.OrderTwelve.Batch3
import equational_theories.Spectrum.Equation1279.OrderTwelve.Batch4

namespace Spectrum.E1279.OrderTwelve
set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem unsat (i : Fin 35) : (natFormula i).Unsat := by
  fin_cases i
  · exact Batch2.unsat 0
  · exact Batch0.unsat 0
  · exact Batch3.unsat 0
  · exact Batch0.unsat 1
  · exact Batch3.unsat 1
  · exact Batch1.unsat 0
  · exact Batch1.unsat 1
  · exact Batch0.unsat 2
  · exact Batch0.unsat 3
  · exact Batch4.unsat 0
  · exact Batch3.unsat 2
  · exact Batch3.unsat 3
  · exact Batch2.unsat 1
  · exact Batch1.unsat 2
  · exact Batch2.unsat 2
  · exact Batch4.unsat 1
  · exact Batch0.unsat 4
  · exact Batch3.unsat 4
  · exact Batch1.unsat 3
  · exact Batch3.unsat 5
  · exact Batch4.unsat 2
  · exact Batch1.unsat 4
  · exact Batch4.unsat 3
  · exact Batch2.unsat 3
  · exact Batch4.unsat 4
  · exact Batch4.unsat 5
  · exact Batch0.unsat 5
  · exact Batch2.unsat 4
  · exact Batch0.unsat 6
  · exact Batch2.unsat 5
  · exact Batch1.unsat 5
  · exact Batch1.unsat 6
  · exact Batch2.unsat 6
  · exact Batch4.unsat 6
  · exact Batch3.unsat 6
spectrum_assert unsat complete
end Spectrum.E1279.OrderTwelve
