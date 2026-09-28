import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 594f58d7882da58e3f52dfecaecc369c65ee50288508b950fe92531e572c88b7
Expanded proof SHA-256: 5393495cf680d01645fd262c8f65a42333b07db64c90ad2a320a081d2032c2d7. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank7Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank7_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank7Zero1 :
    check proofRank7Zero1 (CNF.natRankFormula 10 7 true) = true := by
  native_decide

theorem unsatRank7Zero1 : (CNF.natRankFormula 10 7 true).Unsat :=
  check_sound proofRank7Zero1 _ checkRank7Zero1

end Spectrum.E1483.OrderTen.Refutation
