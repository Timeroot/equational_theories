import equational_theories.Spectrum.FiniteTableEncoding
import equational_theories.Spectrum.SmallModelNormalization
import equational_theories.Equations.All

/-! Generated exhaustive refutation, verified by Lean's registered native LRAT checker. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
namespace Spectrum.FiniteExclusion.E1483N6
open FiniteTableEncoding.N6
def test (a0 a1 a2 a3 a4 a5 : BitVec 18) : Prop :=
  (op a0 a1 a2 a3 a4 a5 0 0 = 0 ∨ op a0 a1 a2 a3 a4 a5 0 0 = 1) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 0 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 0 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 0 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 0 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 0 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 0 5))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 1 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 1 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 1 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 1 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 1 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 1 5))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 2 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 2 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 2 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 2 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 2 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 2 5))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 3 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 3 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 3 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 3 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 3 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 3 5))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 4 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 4 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 4 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 4 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 4 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 4 5))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 5 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 5 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 5 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 5 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 5 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 0) (op a0 a1 a2 a3 a4 a5 0 (op a0 a1 a2 a3 a4 a5 5 5))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 0 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 0 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 0 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 0 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 0 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 0 5))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 1 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 1 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 1 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 1 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 1 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 1 5))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 2 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 2 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 2 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 2 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 2 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 2 5))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 3 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 3 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 3 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 3 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 3 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 3 5))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 4 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 4 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 4 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 4 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 4 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 4 5))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 5 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 5 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 5 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 5 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 5 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 1) (op a0 a1 a2 a3 a4 a5 1 (op a0 a1 a2 a3 a4 a5 5 5))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 0 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 0 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 0 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 0 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 0 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 0 5))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 1 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 1 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 1 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 1 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 1 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 1 5))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 2 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 2 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 2 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 2 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 2 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 2 5))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 3 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 3 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 3 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 3 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 3 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 3 5))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 4 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 4 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 4 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 4 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 4 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 4 5))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 5 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 5 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 5 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 5 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 5 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 2) (op a0 a1 a2 a3 a4 a5 2 (op a0 a1 a2 a3 a4 a5 5 5))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 0 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 0 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 0 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 0 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 0 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 0 5))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 1 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 1 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 1 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 1 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 1 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 1 5))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 2 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 2 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 2 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 2 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 2 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 2 5))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 3 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 3 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 3 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 3 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 3 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 3 5))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 4 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 4 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 4 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 4 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 4 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 4 5))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 5 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 5 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 5 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 5 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 5 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 3) (op a0 a1 a2 a3 a4 a5 3 (op a0 a1 a2 a3 a4 a5 5 5))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 0 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 0 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 0 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 0 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 0 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 0 5))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 1 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 1 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 1 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 1 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 1 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 1 5))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 2 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 2 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 2 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 2 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 2 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 2 5))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 3 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 3 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 3 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 3 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 3 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 3 5))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 4 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 4 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 4 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 4 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 4 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 4 5))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 5 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 5 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 5 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 5 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 5 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 4) (op a0 a1 a2 a3 a4 a5 4 (op a0 a1 a2 a3 a4 a5 5 5))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 0 0))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 0 1))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 0 2))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 0 3))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 0 4))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 0 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 0 5))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 1 0))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 1 1))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 1 2))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 1 3))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 1 4))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 1 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 1 5))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 2 0))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 2 1))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 2 2))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 2 3))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 2 4))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 2 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 2 5))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 3 0))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 3 1))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 3 2))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 3 3))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 3 4))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 3 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 3 5))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 4 0))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 4 1))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 4 2))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 4 3))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 4 4))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 4 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 4 5))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 5 0))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 5 1))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 5 2))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 5 3))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 5 4))) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 (op a0 a1 a2 a3 a4 a5 5 5) (op a0 a1 a2 a3 a4 a5 5 (op a0 a1 a2 a3 a4 a5 5 5)))
@[spectrum_native]
theorem refute (a0 a1 a2 a3 a4 a5 : BitVec 18) : ¬ test a0 a1 a2 a3 a4 a5 := by
  unfold test op clip
  bv_decide (config := { timeout := 300, embeddedConstraintSubst := false })
spectrum_assert refute complete
theorem impossible (M : Magma (Fin 6)) (h : @Equation1483 (Fin 6) M)
    (hd : M.op 0 0 = 0 ∨ M.op 0 0 = 1) : False := by
  have he := encoded_eq M
  apply refute (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)
  unfold test
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)) = bv (0 : Fin 6) ∨
      encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)) = bv (1 : Fin 6)
    simp only [he]
    exact hd.elim (fun h => Or.inl (congrArg bv h)) (fun h => Or.inr (congrArg bv h))
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 0 0)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 0 1)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 0 2)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 0 3)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 0 4)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 0 5)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 1 0)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 1 1)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 1 2)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 1 3)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 1 4)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 1 5)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 2 0)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 2 1)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 2 2)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 2 3)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 2 4)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 2 5)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 3 0)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 3 1)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 3 2)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 3 3)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 3 4)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 3 5)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 4 0)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 4 1)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 4 2)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 4 3)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 4 4)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 4 5)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 5 0)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 5 1)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 5 2)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 5 3)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 5 4)
  · change (bv (0 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 5 5)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 0 0)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 0 1)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 0 2)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 0 3)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 0 4)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 0 5)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 1 0)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 1 1)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 1 2)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 1 3)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 1 4)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 1 5)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 2 0)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 2 1)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 2 2)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 2 3)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 2 4)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 2 5)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 3 0)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 3 1)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 3 2)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 3 3)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 3 4)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 3 5)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 4 0)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 4 1)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 4 2)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 4 3)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 4 4)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 4 5)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 5 0)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 5 1)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 5 2)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 5 3)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 5 4)
  · change (bv (1 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 5 5)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 0 0)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 0 1)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 0 2)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 0 3)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 0 4)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 0 5)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 1 0)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 1 1)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 1 2)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 1 3)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 1 4)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 1 5)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 2 0)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 2 1)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 2 2)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 2 3)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 2 4)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 2 5)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 3 0)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 3 1)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 3 2)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 3 3)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 3 4)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 3 5)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 4 0)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 4 1)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 4 2)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 4 3)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 4 4)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 4 5)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 5 0)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 5 1)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 5 2)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 5 3)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 5 4)
  · change (bv (2 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 5 5)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 0 0)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 0 1)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 0 2)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 0 3)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 0 4)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 0 5)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 1 0)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 1 1)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 1 2)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 1 3)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 1 4)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 1 5)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 2 0)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 2 1)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 2 2)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 2 3)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 2 4)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 2 5)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 3 0)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 3 1)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 3 2)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 3 3)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 3 4)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 3 5)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 4 0)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 4 1)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 4 2)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 4 3)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 4 4)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 4 5)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 5 0)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 5 1)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 5 2)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 5 3)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 5 4)
  · change (bv (3 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 5 5)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 0 0)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 0 1)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 0 2)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 0 3)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 0 4)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 0 5)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 1 0)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 1 1)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 1 2)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 1 3)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 1 4)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 1 5)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 2 0)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 2 1)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 2 2)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 2 3)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 2 4)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 2 5)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 3 0)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 3 1)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 3 2)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 3 3)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 3 4)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 3 5)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 4 0)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 4 1)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 4 2)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 4 3)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 4 4)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 4 5)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 5 0)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 5 1)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 5 2)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 5 3)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 5 4)
  · change (bv (4 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 5 5)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 0 0)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 0 1)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 0 2)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 0 3)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 0 4)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 0 5)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 1 0)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 1 1)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 1 2)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 1 3)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 1 4)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 1 5)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 2 0)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 2 1)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 2 2)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 2 3)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 2 4)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 2 5)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 3 0)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 3 1)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 3 2)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 3 3)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 3 4)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 3 5)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 4 0)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 4 1)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 4 2)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 4 3)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 4 4)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 4 5)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 5 0)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 5 1)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 5 2)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 5 3)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 5 4)
  · change (bv (5 : Fin 6)) = (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 5 5)
end Spectrum.FiniteExclusion.E1483N6
theorem Spectrum.not_order_1483_6 : ¬ Law1483.HasModel 6 := by
  intro h
  obtain ⟨M, hM, hd⟩ := Spectrum.Symmetry.two_label_model Law1483 h 0 1 (by decide)
  exact Spectrum.FiniteExclusion.E1483N6.impossible M ((@Law1483.models_iff _ M).mp hM) hd
spectrum_assert Spectrum.not_order_1483_6 complete
