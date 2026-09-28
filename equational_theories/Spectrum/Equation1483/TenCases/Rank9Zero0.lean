import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: f8023cde45bed7cdeec6c35a31581a0313f05eaa43ec16dcdcdac660c7463b1a
Expanded proof SHA-256: e689a57fdf2faae5c3958d1d843af5a471b2fb2544662249fae7837f7f91ef04. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank9Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank9_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank9Zero0 :
    check proofRank9Zero0 (CNF.natRankFormula 10 9 false) = true := by
  native_decide

theorem unsatRank9Zero0 : (CNF.natRankFormula 10 9 false).Unsat :=
  check_sound proofRank9Zero0 _ checkRank9Zero0

end Spectrum.E1483.OrderTen.Refutation
