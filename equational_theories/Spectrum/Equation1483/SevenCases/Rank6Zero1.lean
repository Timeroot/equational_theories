import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 0c1b2391aac259a854a1956f5190cf79fd48cac3b4fd7f4efe523735035e5c5d
Expanded proof SHA-256: 0893c2af362bf785d92f457e8d53b8cbd51ea11af31593386187d938bbe56e32. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank6Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank6_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank6Zero1 :
    check proofRank6Zero1 (CNF.natRankFormula 7 6 true) = true := by
  native_decide

theorem unsatRank6Zero1 : (CNF.natRankFormula 7 6 true).Unsat :=
  check_sound proofRank6Zero1 _ checkRank6Zero1

end Spectrum.E1483.OrderSeven.Refutation
