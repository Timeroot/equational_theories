import equational_theories.Spectrum.FiniteTableEncoding
import equational_theories.Equations.All

/-! Generated exhaustive refutation, verified by Lean's registered native LRAT checker. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
namespace Spectrum.FiniteExclusion.E1483N5
open FiniteTableEncoding.N5
def test (a0 a1 a2 a3 a4 : BitVec 15) : Prop :=
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 0 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 0 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 0 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 0 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 0 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 1 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 1 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 1 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 1 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 1 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 2 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 2 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 2 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 2 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 2 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 3 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 3 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 3 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 3 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 3 4))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 4 0))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 4 1))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 4 2))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 4 3))) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 0) (op a0 a1 a2 a3 a4 0 (op a0 a1 a2 a3 a4 4 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 0 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 0 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 0 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 0 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 0 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 1 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 1 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 1 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 1 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 1 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 2 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 2 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 2 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 2 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 2 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 3 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 3 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 3 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 3 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 3 4))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 4 0))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 4 1))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 4 2))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 4 3))) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 1) (op a0 a1 a2 a3 a4 1 (op a0 a1 a2 a3 a4 4 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 0 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 0 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 0 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 0 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 0 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 1 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 1 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 1 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 1 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 1 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 2 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 2 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 2 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 2 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 2 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 3 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 3 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 3 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 3 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 3 4))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 4 0))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 4 1))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 4 2))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 4 3))) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 2) (op a0 a1 a2 a3 a4 2 (op a0 a1 a2 a3 a4 4 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 0 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 0 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 0 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 0 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 0 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 1 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 1 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 1 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 1 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 1 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 2 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 2 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 2 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 2 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 2 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 3 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 3 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 3 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 3 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 3 4))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 4 0))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 4 1))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 4 2))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 4 3))) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 3) (op a0 a1 a2 a3 a4 3 (op a0 a1 a2 a3 a4 4 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 0 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 0 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 0 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 0 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 0 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 0 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 1 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 1 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 1 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 1 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 1 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 1 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 2 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 2 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 2 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 2 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 2 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 2 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 3 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 3 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 3 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 3 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 3 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 3 4))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 4 0))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 4 1))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 4 2))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 4 3))) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 (op a0 a1 a2 a3 a4 4 4) (op a0 a1 a2 a3 a4 4 (op a0 a1 a2 a3 a4 4 4)))
@[spectrum_native]
theorem refute (a0 a1 a2 a3 a4 : BitVec 15) : ¬ test a0 a1 a2 a3 a4 := by
  unfold test op clip
  bv_decide (config := { timeout := 300, embeddedConstraintSubst := false })
spectrum_assert refute complete
theorem impossible (M : Magma (Fin 5)) (h : @Equation1483 (Fin 5) M) : False := by
  have he := encoded_eq M
  apply refute (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4)
  unfold test
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 0 0)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 0 1)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 0 2)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 0 3)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 0 4)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 1 0)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 1 1)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 1 2)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 1 3)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 1 4)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 2 0)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 2 1)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 2 2)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 2 3)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 2 4)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 3 0)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 3 1)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 3 2)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 3 3)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 3 4)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 4 0)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 4 1)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 4 2)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 4 3)
  · change (bv (0 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5))) (encoded M (bv (0 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 0 4 4)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 0 0)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 0 1)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 0 2)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 0 3)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 0 4)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 1 0)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 1 1)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 1 2)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 1 3)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 1 4)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 2 0)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 2 1)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 2 2)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 2 3)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 2 4)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 3 0)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 3 1)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 3 2)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 3 3)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 3 4)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 4 0)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 4 1)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 4 2)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 4 3)
  · change (bv (1 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5))) (encoded M (bv (1 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 1 4 4)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 0 0)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 0 1)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 0 2)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 0 3)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 0 4)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 1 0)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 1 1)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 1 2)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 1 3)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 1 4)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 2 0)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 2 1)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 2 2)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 2 3)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 2 4)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 3 0)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 3 1)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 3 2)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 3 3)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 3 4)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 4 0)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 4 1)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 4 2)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 4 3)
  · change (bv (2 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5))) (encoded M (bv (2 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 2 4 4)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 0 0)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 0 1)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 0 2)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 0 3)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 0 4)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 1 0)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 1 1)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 1 2)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 1 3)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 1 4)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 2 0)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 2 1)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 2 2)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 2 3)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 2 4)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 3 0)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 3 1)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 3 2)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 3 3)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 3 4)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 4 0)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 4 1)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 4 2)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 4 3)
  · change (bv (3 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5))) (encoded M (bv (3 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 3 4 4)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 0 0)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 0 1)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 0 2)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 0 3)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (0 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 0 4)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 1 0)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 1 1)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 1 2)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 1 3)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (1 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 1 4)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 2 0)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 2 1)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 2 2)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 2 3)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (2 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 2 4)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 3 0)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 3 1)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 3 2)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 3 3)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (3 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 3 4)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (0 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 4 0)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (1 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 4 1)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (2 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 4 2)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (3 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 4 3)
  · change (bv (4 : Fin 5)) = (encoded M (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5))) (encoded M (bv (4 : Fin 5)) (encoded M (bv (4 : Fin 5)) (bv (4 : Fin 5)))))
    simp only [he]
    exact congrArg bv (h 4 4 4)
end Spectrum.FiniteExclusion.E1483N5
theorem Spectrum.not_order_1483_5 : ¬ Law1483.HasModel 5 := by
  rintro ⟨M, hM⟩
  exact Spectrum.FiniteExclusion.E1483N5.impossible M ((@Law1483.models_iff _ M).mp hM)
spectrum_assert Spectrum.not_order_1483_5 complete
