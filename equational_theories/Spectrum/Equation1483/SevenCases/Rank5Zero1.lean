import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 8fad63e8138c5ebe195288ecdf47706b08fa6ab16478c9fa5351be8b224c7243
Expanded proof SHA-256: 7aba014d29c9eed6186d03d9322e26c9e3a9e43cf65d1f3b41d2cd41b6d33cf3. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank5Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank5_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank5Zero1 :
    check proofRank5Zero1 (CNF.natRankFormula 7 5 true) = true := by
  native_decide

theorem unsatRank5Zero1 : (CNF.natRankFormula 7 5 true).Unsat :=
  check_sound proofRank5Zero1 _ checkRank5Zero1

end Spectrum.E1483.OrderSeven.Refutation
