import equational_theories.Spectrum.SmallPairs.ChainRows
import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.VecNotation

/-! Generated canonical rows; coverage is verified in Canonical.lean. -/
namespace Spectrum.E667.IdempotentFifteen

def row : Fin 13 → Fin 15 → Fin 15 :=
  ![![0,2,3,1,5,6,4,8,9,7,11,12,13,14,10],
    ![0,2,3,1,5,6,4,8,9,10,7,12,13,14,11],
    ![0,2,3,1,5,6,4,8,9,10,11,12,13,14,7],
    ![0,2,3,1,5,6,7,4,9,10,11,12,13,14,8],
    ![0,2,3,1,5,6,7,8,4,10,11,12,13,14,9],
    ![0,2,3,1,5,6,7,8,9,10,11,12,13,14,4],
    ![0,2,3,4,1,6,7,8,5,10,11,12,13,14,9],
    ![0,2,3,4,1,6,7,8,9,5,11,12,13,14,10],
    ![0,2,3,4,1,6,7,8,9,10,11,12,13,14,5],
    ![0,2,3,4,5,1,7,8,9,10,11,12,13,14,6],
    ![0,2,3,4,5,6,1,8,9,10,11,12,13,14,7],
    ![0,2,3,4,5,6,7,1,9,10,11,12,13,14,8],
    ![0,2,3,4,5,6,7,8,9,10,11,12,13,14,1]]

def rows : List (Fin 15 → Fin 15) := (List.finRange 13).map row
end Spectrum.E667.IdempotentFifteen
