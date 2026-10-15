import equational_theories.Spectrum.Equation1483.OrderTwelve.SecondLexEncoding
import equational_theories.Spectrum.SmallOrders.CaseAssembly

/-! Eight short refutations replace one large rank-three refutation. Splitting
only the first two row entries suffices except at the prefix `(2,2)`, where the
third entry is also fixed. A separate certificate checks exhaustive coverage. -/
namespace Spectrum.E1483.OrderTwelve.RankThree
open Std.Sat Spectrum.SmallOrders.CaseAssembly

def base : CNF Nat := SecondLexEncoding.strongNat false 3 false []

/-- Zero-based table atom indices: `(0,j,v)` has index `12*j+v`. -/
def caseData : List (String × List Nat) := [
  ("P11",[13,25]),("P12",[13,26]),("P13",[13,27]),("P21",[14,25]),
  ("P221",[14,26,37]),("P222",[14,26,38]),("P223",[14,26,39]),("P23",[14,27])]

def patterns : List (List Nat) := caseData.map Prod.snd
def branch (units : List Nat) : CNF Nat := caseFormula base units
def coverage : CNF Nat := coverFormula base patterns
end Spectrum.E1483.OrderTwelve.RankThree
