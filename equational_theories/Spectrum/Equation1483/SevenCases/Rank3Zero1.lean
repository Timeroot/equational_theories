import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: f60d4d597e26ab63b57ef516d678cf39cf3c5bb420ab2242dffba7c355e8287a
Expanded proof SHA-256: e767bf4d0321bc63ec9a9d4412f8535e7198a6a88a3bd2eb86a3f52df0d27382. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank3Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank3_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank3Zero1 :
    check proofRank3Zero1 (CNF.natRankFormula 7 3 true) = true := by
  native_decide

theorem unsatRank3Zero1 : (CNF.natRankFormula 7 3 true).Unsat :=
  check_sound proofRank3Zero1 _ checkRank3Zero1

end Spectrum.E1483.OrderSeven.Refutation
