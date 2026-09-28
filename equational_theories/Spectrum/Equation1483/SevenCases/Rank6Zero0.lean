import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 98cf313326174f38fdd50da2770517cb1cce73d07902cb58eab99fb8079bdd71
Expanded proof SHA-256: dcc7b3d7c874212a4dc1836da5ce2ddd12c9f655c6f9a5eb3990eb2cf173dc79. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank6Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank6_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank6Zero0 :
    check proofRank6Zero0 (CNF.natRankFormula 7 6 false) = true := by
  native_decide

theorem unsatRank6Zero0 : (CNF.natRankFormula 7 6 false).Unsat :=
  check_sound proofRank6Zero0 _ checkRank6Zero0

end Spectrum.E1483.OrderSeven.Refutation
