import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 6a8e558af208d388fb526f6b7d55fd0e512cf76b3d397e92dea9787fb75100ac
Expanded proof SHA-256: fcbfcfebdd9b299532731101878118e6bc8fa99488794496b10bb394c4ed73b2. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank2Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank2_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank2Zero0 :
    check proofRank2Zero0 (CNF.natRankFormula 10 2 false) = true := by
  native_decide

theorem unsatRank2Zero0 : (CNF.natRankFormula 10 2 false).Unsat :=
  check_sound proofRank2Zero0 _ checkRank2Zero0

end Spectrum.E1483.OrderTen.Refutation
