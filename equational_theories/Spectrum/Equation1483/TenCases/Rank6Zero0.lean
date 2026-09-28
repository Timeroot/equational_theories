import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 0f11b26c3c1d2efc20026786b65abd31bf619724df89f85dd2c420961b720d9b
Expanded proof SHA-256: 448968d0e93338cbe6d085d6208caadaf0a87aff8718dab4cb85d88a02907cbb. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank6Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank6_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank6Zero0 :
    check proofRank6Zero0 (CNF.natRankFormula 10 6 false) = true := by
  native_decide

theorem unsatRank6Zero0 : (CNF.natRankFormula 10 6 false).Unsat :=
  check_sound proofRank6Zero0 _ checkRank6Zero0

end Spectrum.E1483.OrderTen.Refutation
