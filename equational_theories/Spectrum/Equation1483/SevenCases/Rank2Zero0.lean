import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 210b6a63c6e6f30158d5d8e83fb960145589f3c3da3dd3c724516350a35ba692
Expanded proof SHA-256: ca898aaa89c8aa24d0a7fe682a11ded60c8e89c630a30e7fb98478b74fd182b2. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank2Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank2_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank2Zero0 :
    check proofRank2Zero0 (CNF.natRankFormula 7 2 false) = true := by
  native_decide

theorem unsatRank2Zero0 : (CNF.natRankFormula 7 2 false).Unsat :=
  check_sound proofRank2Zero0 _ checkRank2Zero0

end Spectrum.E1483.OrderSeven.Refutation
