import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 06982d0b78bbd986d9b12f11058a4525a89c8580a1f844bbbe9be694b22c313d
Expanded proof SHA-256: 3083232659d241e04b762c622e33619fa8243c824a7441cbdabec9621aac7279. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank6Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank6_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank6Zero1 :
    check proofRank6Zero1 (CNF.natRankFormula 10 6 true) = true := by
  native_decide

theorem unsatRank6Zero1 : (CNF.natRankFormula 10 6 true).Unsat :=
  check_sound proofRank6Zero1 _ checkRank6Zero1

end Spectrum.E1483.OrderTen.Refutation
