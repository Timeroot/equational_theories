import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: cf568e441fe98d45b68a372a3aca86522146ec622459e3773177034a4c29aacd
Expanded proof SHA-256: 32d67a2cccba30ee4d126da525ef9f3e32f9a6bfe71f9e9a47bf97c6be7cc39e. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank9Zero1 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank9_zero1.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank9Zero1 :
    check proofRank9Zero1 (CNF.natRankFormula 10 9 true) = true := by
  native_decide

theorem unsatRank9Zero1 : (CNF.natRankFormula 10 9 true).Unsat :=
  check_sound proofRank9Zero1 _ checkRank9Zero1

end Spectrum.E1483.OrderTen.Refutation
