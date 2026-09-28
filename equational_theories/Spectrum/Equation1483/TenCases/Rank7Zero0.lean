import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 87f2880b848fafbf854ad0ba155b34a644bc0eb378d89462cbf31f854b76a7fa
Expanded proof SHA-256: 99ec4712c51c7ef3d1e006bccd62e0780b3d640a45e17bb375f7da4b03fa4ae1. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank7Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank7_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank7Zero0 :
    check proofRank7Zero0 (CNF.natRankFormula 10 7 false) = true := by
  native_decide

theorem unsatRank7Zero0 : (CNF.natRankFormula 10 7 false).Unsat :=
  check_sound proofRank7Zero0 _ checkRank7Zero0

end Spectrum.E1483.OrderTen.Refutation
