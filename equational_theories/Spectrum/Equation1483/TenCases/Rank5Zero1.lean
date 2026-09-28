import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: c2088312e9ec16c6567513b7e78bbde7fefdd9183b27286a461d2f396ce41387
Expanded proof SHA-256: 388c52a70813f31c06e6444a004dfe0f7deb9ef9b26103b33586ce8893a9849c. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank5Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank5_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank5Zero1 :
    check proofRank5Zero1 (CNF.natRankFormula 10 5 true) = true := by
  native_decide

theorem unsatRank5Zero1 : (CNF.natRankFormula 10 5 true).Unsat :=
  check_sound proofRank5Zero1 _ checkRank5Zero1

end Spectrum.E1483.OrderTen.Refutation
