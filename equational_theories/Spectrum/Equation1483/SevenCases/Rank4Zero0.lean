import equational_theories.Spectrum.Equation1483.SevenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: dc51cce2f607762406ecc4db6a40bc68cbd0bed8a12abd8da229164a22fb21d3
Expanded proof SHA-256: 8ae93d8fb5f3d0a6ab17470549ce1e39f30bb0790f39eecae54678051d136b41. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderSeven.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank4Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_seven_lrat/seven_rank4_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank4Zero0 :
    check proofRank4Zero0 (CNF.natRankFormula 7 4 false) = true := by
  native_decide

theorem unsatRank4Zero0 : (CNF.natRankFormula 7 4 false).Unsat :=
  check_sound proofRank4Zero0 _ checkRank4Zero0

end Spectrum.E1483.OrderSeven.Refutation
