import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: fea5118547f64606dc732d9f23f588f9d90c2df9403c238b20158a904250249e
Expanded proof SHA-256: b711fb78e2c941b394cb0fd4294b6444c12157be1b0c04d6d3528eade0d31f6e. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank3Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank3_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank3Zero0 :
    check proofRank3Zero0 (CNF.natRankFormula 7 3 false) = true := by
  native_decide

theorem unsatRank3Zero0 : (CNF.natRankFormula 7 3 false).Unsat :=
  check_sound proofRank3Zero0 _ checkRank3Zero0

end Spectrum.E1483.OrderSeven.Refutation
