import equational_theories.Equations.All
import Mathlib.Data.Fin.VecNotation

/-! The idempotent-free eight-element E667 quasigroup, in chain-labelled form.
It is the affine operation `3x + 2y + 1` over F₈, where the binary element 2
satisfies `t³ + t + 1 = 0`, relabelled along the first row. -/
namespace Spectrum.E667.Eight
abbrev K := Fin 8
def quotient : K → K → K :=
  ![![1,2,3,4,5,6,0,7],
    ![5,0,4,3,1,7,2,6],
    ![4,7,5,1,3,0,6,2],
    ![2,1,6,7,0,3,5,4],
    ![7,4,0,2,6,5,3,1],
    ![3,6,1,5,4,2,7,0],
    ![6,3,2,0,7,1,4,5],
    ![0,5,7,6,2,4,1,3]]

end Spectrum.E667.Eight
