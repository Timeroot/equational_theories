import equational_theories.Spectrum.Equation1483.TenSAT
import equational_theories.Definability.IncludeGzip
import equational_theories.Spectrum.Status

/- Generated certificate replay. CNF SHA-256: ba185c00836aaade95e3b19eb283ccd69408fa410abdb2ebe9f4b0e054b60ac6
Expanded proof SHA-256: 627674fc95bbffffe0b5950c1f2504eea60e272f1e9b2855b7bee5a0c1264f82. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Spectrum.E1483.OrderTen.Refutation
open Std.Sat Std.Tactic.BVDecide LRAT

private def proofRank4Zero0 : Array IntAction :=
  (parseLRATProof (include_gzip_str "../../../../data/spectrum/1483_ten_lrat/ten_rank4_zero0.lrat.gz").toUTF8).toOption.getD #[]

@[spectrum_native]
theorem checkRank4Zero0 :
    check proofRank4Zero0 (CNF.natRankFormula 10 4 false) = true := by
  native_decide

theorem unsatRank4Zero0 : (CNF.natRankFormula 10 4 false).Unsat :=
  check_sound proofRank4Zero0 _ checkRank4Zero0

end Spectrum.E1483.OrderTen.Refutation
