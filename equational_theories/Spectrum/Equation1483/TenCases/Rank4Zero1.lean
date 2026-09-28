import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 43a1f7a2d6fd464715670b0c33cd4d8825967c939e81484a39e57b308e7dc5a8
Expanded proof SHA-256: d381bd8f8f0c6bf86571a55f21786fbbb288cf63e8d42c5401fcbe4a6347749b. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank4Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank4_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank4Zero1 :
    check proofRank4Zero1 (CNF.natRankFormula 10 4 true) = true := by
  native_decide

theorem unsatRank4Zero1 : (CNF.natRankFormula 10 4 true).Unsat :=
  check_sound proofRank4Zero1 _ checkRank4Zero1

end Spectrum.E1483.OrderTen.Refutation
