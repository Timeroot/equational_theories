import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: ab47ee6118dc0f3945267a260acd07f4cf5669dd2259a49a62bffc9c5cad68ee
Expanded proof SHA-256: 05f9129361e95b224fa11dae1fe865d6ac2d657c3907e1b83d29dcece6dafdbf. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank5Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank5_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank5Zero0 :
    check proofRank5Zero0 (CNF.natRankFormula 10 5 false) = true := by
  native_decide

theorem unsatRank5Zero0 : (CNF.natRankFormula 10 5 false).Unsat :=
  check_sound proofRank5Zero0 _ checkRank5Zero0

end Spectrum.E1483.OrderTen.Refutation
