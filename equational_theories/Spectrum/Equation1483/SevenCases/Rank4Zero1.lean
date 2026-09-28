import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: b34bcd50f0cd8c0fa44da0897024bb92a150e616a5047b8205599e238f29434a
Expanded proof SHA-256: 7323e30e2543064783de65c7dbce0bcb80aa42b40bacbdbdc06da7aa8d49b42c. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank4Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank4_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank4Zero1 :
    check proofRank4Zero1 (CNF.natRankFormula 7 4 true) = true := by
  native_decide

theorem unsatRank4Zero1 : (CNF.natRankFormula 7 4 true).Unsat :=
  check_sound proofRank4Zero1 _ checkRank4Zero1

end Spectrum.E1483.OrderSeven.Refutation
