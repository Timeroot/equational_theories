import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 596529cdfdf7f5797d86f4820165fd4ca24ff11253d77fe2ed35ac129756971a
Expanded proof SHA-256: b0b5a344fdde44d1222d1c03ac0e7b65497e71b034fd5d11d6bceec2b502f17b. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank3Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank3_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank3Zero0 :
    check proofRank3Zero0 (CNF.natRankFormula 10 3 false) = true := by
  native_decide

theorem unsatRank3Zero0 : (CNF.natRankFormula 10 3 false).Unsat :=
  check_sound proofRank3Zero0 _ checkRank3Zero0

end Spectrum.E1483.OrderTen.Refutation
