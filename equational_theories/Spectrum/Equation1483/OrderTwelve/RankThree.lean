import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.P11
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.P12
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.P13
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.P21
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.P221
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.P222
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.P223
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.P23
import equational_theories.Spectrum.Equation1483.OrderTwelve.RankThree.Certificates.Coverage

/-! The minimum-rank-three case has eight independently checked short branches.
The separate coverage certificate proves that their assumptions exhaust the
normalized formula, without trusting the external case selection. -/
namespace Spectrum.E1483.OrderTwelve.RankThree
open Spectrum.SmallOrders.CaseAssembly

theorem unsat : base.Unsat := by
  apply unsat_of_cases base patterns
  · intro us hu
    simp [patterns,caseData] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Certificates.P11.unsat
    · exact Certificates.P12.unsat
    · exact Certificates.P13.unsat
    · exact Certificates.P21.unsat
    · exact Certificates.P221.unsat
    · exact Certificates.P222.unsat
    · exact Certificates.P223.unsat
    · exact Certificates.P23.unsat
  · exact Certificates.Coverage.unsat

theorem no_model (f : Fin 12 → Fin 12 → Fin 12) (h : NormalForm f 3 false)
    (hl : SecondLexNormalization.SecondLex f 3 false) : False := by
  exact SecondLexEncoding.no_model_strong false 3 false [] unsat f h hl (by simp)

spectrum_assert no_model complete
end Spectrum.E1483.OrderTwelve.RankThree
