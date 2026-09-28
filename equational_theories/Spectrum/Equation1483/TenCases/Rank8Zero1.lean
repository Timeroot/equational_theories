import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 7684cdb94ef60d5a45daf743b4727b3061897a3c52ed73d45fed26f0d2094ac1
Expanded proof SHA-256: 42e646ab1bdf1f7c9e17a13ba62c2a0c8232a1622d09ac1a738af60386b9ff2b. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank8Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank8_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank8Zero1 :
    check proofRank8Zero1 (CNF.natRankFormula 10 8 true) = true := by
  native_decide

theorem unsatRank8Zero1 : (CNF.natRankFormula 10 8 true).Unsat :=
  check_sound proofRank8Zero1 _ checkRank8Zero1

end Spectrum.E1483.OrderTen.Refutation
