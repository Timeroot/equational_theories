import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 0873ecbb8ff3f4712c77cd2ec8fee560237b54bec83971729bf1152784534ef2
Expanded proof SHA-256: a4bfa6ebf740742b18aabee891798e06aef45256d1392f059de4aa4198d78c47. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank8Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank8_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank8Zero0 :
    check proofRank8Zero0 (CNF.natRankFormula 10 8 false) = true := by
  native_decide

theorem unsatRank8Zero0 : (CNF.natRankFormula 10 8 false).Unsat :=
  check_sound proofRank8Zero0 _ checkRank8Zero0

end Spectrum.E1483.OrderTen.Refutation
