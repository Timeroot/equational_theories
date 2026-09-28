import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: 9c88d7dfb15355925b8291d1818700bd704131ea40080de39a71a64b0601aa00
Expanded proof SHA-256: 59eefdfd59fd3ead473da548871ca49d17fdd0ba2dbbb0218c377c6a034bf89f. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank5Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank5_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank5Zero0 :
    check proofRank5Zero0 (CNF.natRankFormula 7 5 false) = true := by
  native_decide

theorem unsatRank5Zero0 : (CNF.natRankFormula 7 5 false).Unsat :=
  check_sound proofRank5Zero0 _ checkRank5Zero0

end Spectrum.E1483.OrderSeven.Refutation
