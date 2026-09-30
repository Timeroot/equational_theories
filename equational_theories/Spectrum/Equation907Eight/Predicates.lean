import equational_theories.Spectrum.Equation907Eight.Table

set_option maxHeartbeats 16000000
set_option maxRecDepth 32768

namespace Spectrum.E907Eight

def testLaw (a b c d e f g h : BitVec 24) : Prop :=
  (0 : BitVec 3) = (op a b c d e f g h 0 (op a b c d e f g h (op a b c d e f g h 0 0) (op a b c d e f g h 0 0))) ∧
  (0 : BitVec 3) = (op a b c d e f g h 1 (op a b c d e f g h (op a b c d e f g h 1 0) (op a b c d e f g h 0 1))) ∧
  (0 : BitVec 3) = (op a b c d e f g h 2 (op a b c d e f g h (op a b c d e f g h 2 0) (op a b c d e f g h 0 2))) ∧
  (0 : BitVec 3) = (op a b c d e f g h 3 (op a b c d e f g h (op a b c d e f g h 3 0) (op a b c d e f g h 0 3))) ∧
  (0 : BitVec 3) = (op a b c d e f g h 4 (op a b c d e f g h (op a b c d e f g h 4 0) (op a b c d e f g h 0 4))) ∧
  (0 : BitVec 3) = (op a b c d e f g h 5 (op a b c d e f g h (op a b c d e f g h 5 0) (op a b c d e f g h 0 5))) ∧
  (0 : BitVec 3) = (op a b c d e f g h 6 (op a b c d e f g h (op a b c d e f g h 6 0) (op a b c d e f g h 0 6))) ∧
  (0 : BitVec 3) = (op a b c d e f g h 7 (op a b c d e f g h (op a b c d e f g h 7 0) (op a b c d e f g h 0 7))) ∧
  (1 : BitVec 3) = (op a b c d e f g h 0 (op a b c d e f g h (op a b c d e f g h 0 1) (op a b c d e f g h 1 0))) ∧
  (1 : BitVec 3) = (op a b c d e f g h 1 (op a b c d e f g h (op a b c d e f g h 1 1) (op a b c d e f g h 1 1))) ∧
  (1 : BitVec 3) = (op a b c d e f g h 2 (op a b c d e f g h (op a b c d e f g h 2 1) (op a b c d e f g h 1 2))) ∧
  (1 : BitVec 3) = (op a b c d e f g h 3 (op a b c d e f g h (op a b c d e f g h 3 1) (op a b c d e f g h 1 3))) ∧
  (1 : BitVec 3) = (op a b c d e f g h 4 (op a b c d e f g h (op a b c d e f g h 4 1) (op a b c d e f g h 1 4))) ∧
  (1 : BitVec 3) = (op a b c d e f g h 5 (op a b c d e f g h (op a b c d e f g h 5 1) (op a b c d e f g h 1 5))) ∧
  (1 : BitVec 3) = (op a b c d e f g h 6 (op a b c d e f g h (op a b c d e f g h 6 1) (op a b c d e f g h 1 6))) ∧
  (1 : BitVec 3) = (op a b c d e f g h 7 (op a b c d e f g h (op a b c d e f g h 7 1) (op a b c d e f g h 1 7))) ∧
  (2 : BitVec 3) = (op a b c d e f g h 0 (op a b c d e f g h (op a b c d e f g h 0 2) (op a b c d e f g h 2 0))) ∧
  (2 : BitVec 3) = (op a b c d e f g h 1 (op a b c d e f g h (op a b c d e f g h 1 2) (op a b c d e f g h 2 1))) ∧
  (2 : BitVec 3) = (op a b c d e f g h 2 (op a b c d e f g h (op a b c d e f g h 2 2) (op a b c d e f g h 2 2))) ∧
  (2 : BitVec 3) = (op a b c d e f g h 3 (op a b c d e f g h (op a b c d e f g h 3 2) (op a b c d e f g h 2 3))) ∧
  (2 : BitVec 3) = (op a b c d e f g h 4 (op a b c d e f g h (op a b c d e f g h 4 2) (op a b c d e f g h 2 4))) ∧
  (2 : BitVec 3) = (op a b c d e f g h 5 (op a b c d e f g h (op a b c d e f g h 5 2) (op a b c d e f g h 2 5))) ∧
  (2 : BitVec 3) = (op a b c d e f g h 6 (op a b c d e f g h (op a b c d e f g h 6 2) (op a b c d e f g h 2 6))) ∧
  (2 : BitVec 3) = (op a b c d e f g h 7 (op a b c d e f g h (op a b c d e f g h 7 2) (op a b c d e f g h 2 7))) ∧
  (3 : BitVec 3) = (op a b c d e f g h 0 (op a b c d e f g h (op a b c d e f g h 0 3) (op a b c d e f g h 3 0))) ∧
  (3 : BitVec 3) = (op a b c d e f g h 1 (op a b c d e f g h (op a b c d e f g h 1 3) (op a b c d e f g h 3 1))) ∧
  (3 : BitVec 3) = (op a b c d e f g h 2 (op a b c d e f g h (op a b c d e f g h 2 3) (op a b c d e f g h 3 2))) ∧
  (3 : BitVec 3) = (op a b c d e f g h 3 (op a b c d e f g h (op a b c d e f g h 3 3) (op a b c d e f g h 3 3))) ∧
  (3 : BitVec 3) = (op a b c d e f g h 4 (op a b c d e f g h (op a b c d e f g h 4 3) (op a b c d e f g h 3 4))) ∧
  (3 : BitVec 3) = (op a b c d e f g h 5 (op a b c d e f g h (op a b c d e f g h 5 3) (op a b c d e f g h 3 5))) ∧
  (3 : BitVec 3) = (op a b c d e f g h 6 (op a b c d e f g h (op a b c d e f g h 6 3) (op a b c d e f g h 3 6))) ∧
  (3 : BitVec 3) = (op a b c d e f g h 7 (op a b c d e f g h (op a b c d e f g h 7 3) (op a b c d e f g h 3 7))) ∧
  (4 : BitVec 3) = (op a b c d e f g h 0 (op a b c d e f g h (op a b c d e f g h 0 4) (op a b c d e f g h 4 0))) ∧
  (4 : BitVec 3) = (op a b c d e f g h 1 (op a b c d e f g h (op a b c d e f g h 1 4) (op a b c d e f g h 4 1))) ∧
  (4 : BitVec 3) = (op a b c d e f g h 2 (op a b c d e f g h (op a b c d e f g h 2 4) (op a b c d e f g h 4 2))) ∧
  (4 : BitVec 3) = (op a b c d e f g h 3 (op a b c d e f g h (op a b c d e f g h 3 4) (op a b c d e f g h 4 3))) ∧
  (4 : BitVec 3) = (op a b c d e f g h 4 (op a b c d e f g h (op a b c d e f g h 4 4) (op a b c d e f g h 4 4))) ∧
  (4 : BitVec 3) = (op a b c d e f g h 5 (op a b c d e f g h (op a b c d e f g h 5 4) (op a b c d e f g h 4 5))) ∧
  (4 : BitVec 3) = (op a b c d e f g h 6 (op a b c d e f g h (op a b c d e f g h 6 4) (op a b c d e f g h 4 6))) ∧
  (4 : BitVec 3) = (op a b c d e f g h 7 (op a b c d e f g h (op a b c d e f g h 7 4) (op a b c d e f g h 4 7))) ∧
  (5 : BitVec 3) = (op a b c d e f g h 0 (op a b c d e f g h (op a b c d e f g h 0 5) (op a b c d e f g h 5 0))) ∧
  (5 : BitVec 3) = (op a b c d e f g h 1 (op a b c d e f g h (op a b c d e f g h 1 5) (op a b c d e f g h 5 1))) ∧
  (5 : BitVec 3) = (op a b c d e f g h 2 (op a b c d e f g h (op a b c d e f g h 2 5) (op a b c d e f g h 5 2))) ∧
  (5 : BitVec 3) = (op a b c d e f g h 3 (op a b c d e f g h (op a b c d e f g h 3 5) (op a b c d e f g h 5 3))) ∧
  (5 : BitVec 3) = (op a b c d e f g h 4 (op a b c d e f g h (op a b c d e f g h 4 5) (op a b c d e f g h 5 4))) ∧
  (5 : BitVec 3) = (op a b c d e f g h 5 (op a b c d e f g h (op a b c d e f g h 5 5) (op a b c d e f g h 5 5))) ∧
  (5 : BitVec 3) = (op a b c d e f g h 6 (op a b c d e f g h (op a b c d e f g h 6 5) (op a b c d e f g h 5 6))) ∧
  (5 : BitVec 3) = (op a b c d e f g h 7 (op a b c d e f g h (op a b c d e f g h 7 5) (op a b c d e f g h 5 7))) ∧
  (6 : BitVec 3) = (op a b c d e f g h 0 (op a b c d e f g h (op a b c d e f g h 0 6) (op a b c d e f g h 6 0))) ∧
  (6 : BitVec 3) = (op a b c d e f g h 1 (op a b c d e f g h (op a b c d e f g h 1 6) (op a b c d e f g h 6 1))) ∧
  (6 : BitVec 3) = (op a b c d e f g h 2 (op a b c d e f g h (op a b c d e f g h 2 6) (op a b c d e f g h 6 2))) ∧
  (6 : BitVec 3) = (op a b c d e f g h 3 (op a b c d e f g h (op a b c d e f g h 3 6) (op a b c d e f g h 6 3))) ∧
  (6 : BitVec 3) = (op a b c d e f g h 4 (op a b c d e f g h (op a b c d e f g h 4 6) (op a b c d e f g h 6 4))) ∧
  (6 : BitVec 3) = (op a b c d e f g h 5 (op a b c d e f g h (op a b c d e f g h 5 6) (op a b c d e f g h 6 5))) ∧
  (6 : BitVec 3) = (op a b c d e f g h 6 (op a b c d e f g h (op a b c d e f g h 6 6) (op a b c d e f g h 6 6))) ∧
  (6 : BitVec 3) = (op a b c d e f g h 7 (op a b c d e f g h (op a b c d e f g h 7 6) (op a b c d e f g h 6 7))) ∧
  (7 : BitVec 3) = (op a b c d e f g h 0 (op a b c d e f g h (op a b c d e f g h 0 7) (op a b c d e f g h 7 0))) ∧
  (7 : BitVec 3) = (op a b c d e f g h 1 (op a b c d e f g h (op a b c d e f g h 1 7) (op a b c d e f g h 7 1))) ∧
  (7 : BitVec 3) = (op a b c d e f g h 2 (op a b c d e f g h (op a b c d e f g h 2 7) (op a b c d e f g h 7 2))) ∧
  (7 : BitVec 3) = (op a b c d e f g h 3 (op a b c d e f g h (op a b c d e f g h 3 7) (op a b c d e f g h 7 3))) ∧
  (7 : BitVec 3) = (op a b c d e f g h 4 (op a b c d e f g h (op a b c d e f g h 4 7) (op a b c d e f g h 7 4))) ∧
  (7 : BitVec 3) = (op a b c d e f g h 5 (op a b c d e f g h (op a b c d e f g h 5 7) (op a b c d e f g h 7 5))) ∧
  (7 : BitVec 3) = (op a b c d e f g h 6 (op a b c d e f g h (op a b c d e f g h 6 7) (op a b c d e f g h 7 6))) ∧
  (7 : BitVec 3) = (op a b c d e f g h 7 (op a b c d e f g h (op a b c d e f g h 7 7) (op a b c d e f g h 7 7)))

def testLatin (a b c d e f g h : BitVec 24) : Prop :=
  (op a b c d e f g h 0 0) ≠ (op a b c d e f g h 0 1) ∧
  (op a b c d e f g h 0 0) ≠ (op a b c d e f g h 0 2) ∧
  (op a b c d e f g h 0 0) ≠ (op a b c d e f g h 0 3) ∧
  (op a b c d e f g h 0 0) ≠ (op a b c d e f g h 0 4) ∧
  (op a b c d e f g h 0 0) ≠ (op a b c d e f g h 0 5) ∧
  (op a b c d e f g h 0 0) ≠ (op a b c d e f g h 0 6) ∧
  (op a b c d e f g h 0 0) ≠ (op a b c d e f g h 0 7) ∧
  (op a b c d e f g h 0 1) ≠ (op a b c d e f g h 0 2) ∧
  (op a b c d e f g h 0 1) ≠ (op a b c d e f g h 0 3) ∧
  (op a b c d e f g h 0 1) ≠ (op a b c d e f g h 0 4) ∧
  (op a b c d e f g h 0 1) ≠ (op a b c d e f g h 0 5) ∧
  (op a b c d e f g h 0 1) ≠ (op a b c d e f g h 0 6) ∧
  (op a b c d e f g h 0 1) ≠ (op a b c d e f g h 0 7) ∧
  (op a b c d e f g h 0 2) ≠ (op a b c d e f g h 0 3) ∧
  (op a b c d e f g h 0 2) ≠ (op a b c d e f g h 0 4) ∧
  (op a b c d e f g h 0 2) ≠ (op a b c d e f g h 0 5) ∧
  (op a b c d e f g h 0 2) ≠ (op a b c d e f g h 0 6) ∧
  (op a b c d e f g h 0 2) ≠ (op a b c d e f g h 0 7) ∧
  (op a b c d e f g h 0 3) ≠ (op a b c d e f g h 0 4) ∧
  (op a b c d e f g h 0 3) ≠ (op a b c d e f g h 0 5) ∧
  (op a b c d e f g h 0 3) ≠ (op a b c d e f g h 0 6) ∧
  (op a b c d e f g h 0 3) ≠ (op a b c d e f g h 0 7) ∧
  (op a b c d e f g h 0 4) ≠ (op a b c d e f g h 0 5) ∧
  (op a b c d e f g h 0 4) ≠ (op a b c d e f g h 0 6) ∧
  (op a b c d e f g h 0 4) ≠ (op a b c d e f g h 0 7) ∧
  (op a b c d e f g h 0 5) ≠ (op a b c d e f g h 0 6) ∧
  (op a b c d e f g h 0 5) ≠ (op a b c d e f g h 0 7) ∧
  (op a b c d e f g h 0 6) ≠ (op a b c d e f g h 0 7) ∧
  (op a b c d e f g h 1 0) ≠ (op a b c d e f g h 1 1) ∧
  (op a b c d e f g h 1 0) ≠ (op a b c d e f g h 1 2) ∧
  (op a b c d e f g h 1 0) ≠ (op a b c d e f g h 1 3) ∧
  (op a b c d e f g h 1 0) ≠ (op a b c d e f g h 1 4) ∧
  (op a b c d e f g h 1 0) ≠ (op a b c d e f g h 1 5) ∧
  (op a b c d e f g h 1 0) ≠ (op a b c d e f g h 1 6) ∧
  (op a b c d e f g h 1 0) ≠ (op a b c d e f g h 1 7) ∧
  (op a b c d e f g h 1 1) ≠ (op a b c d e f g h 1 2) ∧
  (op a b c d e f g h 1 1) ≠ (op a b c d e f g h 1 3) ∧
  (op a b c d e f g h 1 1) ≠ (op a b c d e f g h 1 4) ∧
  (op a b c d e f g h 1 1) ≠ (op a b c d e f g h 1 5) ∧
  (op a b c d e f g h 1 1) ≠ (op a b c d e f g h 1 6) ∧
  (op a b c d e f g h 1 1) ≠ (op a b c d e f g h 1 7) ∧
  (op a b c d e f g h 1 2) ≠ (op a b c d e f g h 1 3) ∧
  (op a b c d e f g h 1 2) ≠ (op a b c d e f g h 1 4) ∧
  (op a b c d e f g h 1 2) ≠ (op a b c d e f g h 1 5) ∧
  (op a b c d e f g h 1 2) ≠ (op a b c d e f g h 1 6) ∧
  (op a b c d e f g h 1 2) ≠ (op a b c d e f g h 1 7) ∧
  (op a b c d e f g h 1 3) ≠ (op a b c d e f g h 1 4) ∧
  (op a b c d e f g h 1 3) ≠ (op a b c d e f g h 1 5) ∧
  (op a b c d e f g h 1 3) ≠ (op a b c d e f g h 1 6) ∧
  (op a b c d e f g h 1 3) ≠ (op a b c d e f g h 1 7) ∧
  (op a b c d e f g h 1 4) ≠ (op a b c d e f g h 1 5) ∧
  (op a b c d e f g h 1 4) ≠ (op a b c d e f g h 1 6) ∧
  (op a b c d e f g h 1 4) ≠ (op a b c d e f g h 1 7) ∧
  (op a b c d e f g h 1 5) ≠ (op a b c d e f g h 1 6) ∧
  (op a b c d e f g h 1 5) ≠ (op a b c d e f g h 1 7) ∧
  (op a b c d e f g h 1 6) ≠ (op a b c d e f g h 1 7) ∧
  (op a b c d e f g h 2 0) ≠ (op a b c d e f g h 2 1) ∧
  (op a b c d e f g h 2 0) ≠ (op a b c d e f g h 2 2) ∧
  (op a b c d e f g h 2 0) ≠ (op a b c d e f g h 2 3) ∧
  (op a b c d e f g h 2 0) ≠ (op a b c d e f g h 2 4) ∧
  (op a b c d e f g h 2 0) ≠ (op a b c d e f g h 2 5) ∧
  (op a b c d e f g h 2 0) ≠ (op a b c d e f g h 2 6) ∧
  (op a b c d e f g h 2 0) ≠ (op a b c d e f g h 2 7) ∧
  (op a b c d e f g h 2 1) ≠ (op a b c d e f g h 2 2) ∧
  (op a b c d e f g h 2 1) ≠ (op a b c d e f g h 2 3) ∧
  (op a b c d e f g h 2 1) ≠ (op a b c d e f g h 2 4) ∧
  (op a b c d e f g h 2 1) ≠ (op a b c d e f g h 2 5) ∧
  (op a b c d e f g h 2 1) ≠ (op a b c d e f g h 2 6) ∧
  (op a b c d e f g h 2 1) ≠ (op a b c d e f g h 2 7) ∧
  (op a b c d e f g h 2 2) ≠ (op a b c d e f g h 2 3) ∧
  (op a b c d e f g h 2 2) ≠ (op a b c d e f g h 2 4) ∧
  (op a b c d e f g h 2 2) ≠ (op a b c d e f g h 2 5) ∧
  (op a b c d e f g h 2 2) ≠ (op a b c d e f g h 2 6) ∧
  (op a b c d e f g h 2 2) ≠ (op a b c d e f g h 2 7) ∧
  (op a b c d e f g h 2 3) ≠ (op a b c d e f g h 2 4) ∧
  (op a b c d e f g h 2 3) ≠ (op a b c d e f g h 2 5) ∧
  (op a b c d e f g h 2 3) ≠ (op a b c d e f g h 2 6) ∧
  (op a b c d e f g h 2 3) ≠ (op a b c d e f g h 2 7) ∧
  (op a b c d e f g h 2 4) ≠ (op a b c d e f g h 2 5) ∧
  (op a b c d e f g h 2 4) ≠ (op a b c d e f g h 2 6) ∧
  (op a b c d e f g h 2 4) ≠ (op a b c d e f g h 2 7) ∧
  (op a b c d e f g h 2 5) ≠ (op a b c d e f g h 2 6) ∧
  (op a b c d e f g h 2 5) ≠ (op a b c d e f g h 2 7) ∧
  (op a b c d e f g h 2 6) ≠ (op a b c d e f g h 2 7) ∧
  (op a b c d e f g h 3 0) ≠ (op a b c d e f g h 3 1) ∧
  (op a b c d e f g h 3 0) ≠ (op a b c d e f g h 3 2) ∧
  (op a b c d e f g h 3 0) ≠ (op a b c d e f g h 3 3) ∧
  (op a b c d e f g h 3 0) ≠ (op a b c d e f g h 3 4) ∧
  (op a b c d e f g h 3 0) ≠ (op a b c d e f g h 3 5) ∧
  (op a b c d e f g h 3 0) ≠ (op a b c d e f g h 3 6) ∧
  (op a b c d e f g h 3 0) ≠ (op a b c d e f g h 3 7) ∧
  (op a b c d e f g h 3 1) ≠ (op a b c d e f g h 3 2) ∧
  (op a b c d e f g h 3 1) ≠ (op a b c d e f g h 3 3) ∧
  (op a b c d e f g h 3 1) ≠ (op a b c d e f g h 3 4) ∧
  (op a b c d e f g h 3 1) ≠ (op a b c d e f g h 3 5) ∧
  (op a b c d e f g h 3 1) ≠ (op a b c d e f g h 3 6) ∧
  (op a b c d e f g h 3 1) ≠ (op a b c d e f g h 3 7) ∧
  (op a b c d e f g h 3 2) ≠ (op a b c d e f g h 3 3) ∧
  (op a b c d e f g h 3 2) ≠ (op a b c d e f g h 3 4) ∧
  (op a b c d e f g h 3 2) ≠ (op a b c d e f g h 3 5) ∧
  (op a b c d e f g h 3 2) ≠ (op a b c d e f g h 3 6) ∧
  (op a b c d e f g h 3 2) ≠ (op a b c d e f g h 3 7) ∧
  (op a b c d e f g h 3 3) ≠ (op a b c d e f g h 3 4) ∧
  (op a b c d e f g h 3 3) ≠ (op a b c d e f g h 3 5) ∧
  (op a b c d e f g h 3 3) ≠ (op a b c d e f g h 3 6) ∧
  (op a b c d e f g h 3 3) ≠ (op a b c d e f g h 3 7) ∧
  (op a b c d e f g h 3 4) ≠ (op a b c d e f g h 3 5) ∧
  (op a b c d e f g h 3 4) ≠ (op a b c d e f g h 3 6) ∧
  (op a b c d e f g h 3 4) ≠ (op a b c d e f g h 3 7) ∧
  (op a b c d e f g h 3 5) ≠ (op a b c d e f g h 3 6) ∧
  (op a b c d e f g h 3 5) ≠ (op a b c d e f g h 3 7) ∧
  (op a b c d e f g h 3 6) ≠ (op a b c d e f g h 3 7) ∧
  (op a b c d e f g h 4 0) ≠ (op a b c d e f g h 4 1) ∧
  (op a b c d e f g h 4 0) ≠ (op a b c d e f g h 4 2) ∧
  (op a b c d e f g h 4 0) ≠ (op a b c d e f g h 4 3) ∧
  (op a b c d e f g h 4 0) ≠ (op a b c d e f g h 4 4) ∧
  (op a b c d e f g h 4 0) ≠ (op a b c d e f g h 4 5) ∧
  (op a b c d e f g h 4 0) ≠ (op a b c d e f g h 4 6) ∧
  (op a b c d e f g h 4 0) ≠ (op a b c d e f g h 4 7) ∧
  (op a b c d e f g h 4 1) ≠ (op a b c d e f g h 4 2) ∧
  (op a b c d e f g h 4 1) ≠ (op a b c d e f g h 4 3) ∧
  (op a b c d e f g h 4 1) ≠ (op a b c d e f g h 4 4) ∧
  (op a b c d e f g h 4 1) ≠ (op a b c d e f g h 4 5) ∧
  (op a b c d e f g h 4 1) ≠ (op a b c d e f g h 4 6) ∧
  (op a b c d e f g h 4 1) ≠ (op a b c d e f g h 4 7) ∧
  (op a b c d e f g h 4 2) ≠ (op a b c d e f g h 4 3) ∧
  (op a b c d e f g h 4 2) ≠ (op a b c d e f g h 4 4) ∧
  (op a b c d e f g h 4 2) ≠ (op a b c d e f g h 4 5) ∧
  (op a b c d e f g h 4 2) ≠ (op a b c d e f g h 4 6) ∧
  (op a b c d e f g h 4 2) ≠ (op a b c d e f g h 4 7) ∧
  (op a b c d e f g h 4 3) ≠ (op a b c d e f g h 4 4) ∧
  (op a b c d e f g h 4 3) ≠ (op a b c d e f g h 4 5) ∧
  (op a b c d e f g h 4 3) ≠ (op a b c d e f g h 4 6) ∧
  (op a b c d e f g h 4 3) ≠ (op a b c d e f g h 4 7) ∧
  (op a b c d e f g h 4 4) ≠ (op a b c d e f g h 4 5) ∧
  (op a b c d e f g h 4 4) ≠ (op a b c d e f g h 4 6) ∧
  (op a b c d e f g h 4 4) ≠ (op a b c d e f g h 4 7) ∧
  (op a b c d e f g h 4 5) ≠ (op a b c d e f g h 4 6) ∧
  (op a b c d e f g h 4 5) ≠ (op a b c d e f g h 4 7) ∧
  (op a b c d e f g h 4 6) ≠ (op a b c d e f g h 4 7) ∧
  (op a b c d e f g h 5 0) ≠ (op a b c d e f g h 5 1) ∧
  (op a b c d e f g h 5 0) ≠ (op a b c d e f g h 5 2) ∧
  (op a b c d e f g h 5 0) ≠ (op a b c d e f g h 5 3) ∧
  (op a b c d e f g h 5 0) ≠ (op a b c d e f g h 5 4) ∧
  (op a b c d e f g h 5 0) ≠ (op a b c d e f g h 5 5) ∧
  (op a b c d e f g h 5 0) ≠ (op a b c d e f g h 5 6) ∧
  (op a b c d e f g h 5 0) ≠ (op a b c d e f g h 5 7) ∧
  (op a b c d e f g h 5 1) ≠ (op a b c d e f g h 5 2) ∧
  (op a b c d e f g h 5 1) ≠ (op a b c d e f g h 5 3) ∧
  (op a b c d e f g h 5 1) ≠ (op a b c d e f g h 5 4) ∧
  (op a b c d e f g h 5 1) ≠ (op a b c d e f g h 5 5) ∧
  (op a b c d e f g h 5 1) ≠ (op a b c d e f g h 5 6) ∧
  (op a b c d e f g h 5 1) ≠ (op a b c d e f g h 5 7) ∧
  (op a b c d e f g h 5 2) ≠ (op a b c d e f g h 5 3) ∧
  (op a b c d e f g h 5 2) ≠ (op a b c d e f g h 5 4) ∧
  (op a b c d e f g h 5 2) ≠ (op a b c d e f g h 5 5) ∧
  (op a b c d e f g h 5 2) ≠ (op a b c d e f g h 5 6) ∧
  (op a b c d e f g h 5 2) ≠ (op a b c d e f g h 5 7) ∧
  (op a b c d e f g h 5 3) ≠ (op a b c d e f g h 5 4) ∧
  (op a b c d e f g h 5 3) ≠ (op a b c d e f g h 5 5) ∧
  (op a b c d e f g h 5 3) ≠ (op a b c d e f g h 5 6) ∧
  (op a b c d e f g h 5 3) ≠ (op a b c d e f g h 5 7) ∧
  (op a b c d e f g h 5 4) ≠ (op a b c d e f g h 5 5) ∧
  (op a b c d e f g h 5 4) ≠ (op a b c d e f g h 5 6) ∧
  (op a b c d e f g h 5 4) ≠ (op a b c d e f g h 5 7) ∧
  (op a b c d e f g h 5 5) ≠ (op a b c d e f g h 5 6) ∧
  (op a b c d e f g h 5 5) ≠ (op a b c d e f g h 5 7) ∧
  (op a b c d e f g h 5 6) ≠ (op a b c d e f g h 5 7) ∧
  (op a b c d e f g h 6 0) ≠ (op a b c d e f g h 6 1) ∧
  (op a b c d e f g h 6 0) ≠ (op a b c d e f g h 6 2) ∧
  (op a b c d e f g h 6 0) ≠ (op a b c d e f g h 6 3) ∧
  (op a b c d e f g h 6 0) ≠ (op a b c d e f g h 6 4) ∧
  (op a b c d e f g h 6 0) ≠ (op a b c d e f g h 6 5) ∧
  (op a b c d e f g h 6 0) ≠ (op a b c d e f g h 6 6) ∧
  (op a b c d e f g h 6 0) ≠ (op a b c d e f g h 6 7) ∧
  (op a b c d e f g h 6 1) ≠ (op a b c d e f g h 6 2) ∧
  (op a b c d e f g h 6 1) ≠ (op a b c d e f g h 6 3) ∧
  (op a b c d e f g h 6 1) ≠ (op a b c d e f g h 6 4) ∧
  (op a b c d e f g h 6 1) ≠ (op a b c d e f g h 6 5) ∧
  (op a b c d e f g h 6 1) ≠ (op a b c d e f g h 6 6) ∧
  (op a b c d e f g h 6 1) ≠ (op a b c d e f g h 6 7) ∧
  (op a b c d e f g h 6 2) ≠ (op a b c d e f g h 6 3) ∧
  (op a b c d e f g h 6 2) ≠ (op a b c d e f g h 6 4) ∧
  (op a b c d e f g h 6 2) ≠ (op a b c d e f g h 6 5) ∧
  (op a b c d e f g h 6 2) ≠ (op a b c d e f g h 6 6) ∧
  (op a b c d e f g h 6 2) ≠ (op a b c d e f g h 6 7) ∧
  (op a b c d e f g h 6 3) ≠ (op a b c d e f g h 6 4) ∧
  (op a b c d e f g h 6 3) ≠ (op a b c d e f g h 6 5) ∧
  (op a b c d e f g h 6 3) ≠ (op a b c d e f g h 6 6) ∧
  (op a b c d e f g h 6 3) ≠ (op a b c d e f g h 6 7) ∧
  (op a b c d e f g h 6 4) ≠ (op a b c d e f g h 6 5) ∧
  (op a b c d e f g h 6 4) ≠ (op a b c d e f g h 6 6) ∧
  (op a b c d e f g h 6 4) ≠ (op a b c d e f g h 6 7) ∧
  (op a b c d e f g h 6 5) ≠ (op a b c d e f g h 6 6) ∧
  (op a b c d e f g h 6 5) ≠ (op a b c d e f g h 6 7) ∧
  (op a b c d e f g h 6 6) ≠ (op a b c d e f g h 6 7) ∧
  (op a b c d e f g h 7 0) ≠ (op a b c d e f g h 7 1) ∧
  (op a b c d e f g h 7 0) ≠ (op a b c d e f g h 7 2) ∧
  (op a b c d e f g h 7 0) ≠ (op a b c d e f g h 7 3) ∧
  (op a b c d e f g h 7 0) ≠ (op a b c d e f g h 7 4) ∧
  (op a b c d e f g h 7 0) ≠ (op a b c d e f g h 7 5) ∧
  (op a b c d e f g h 7 0) ≠ (op a b c d e f g h 7 6) ∧
  (op a b c d e f g h 7 0) ≠ (op a b c d e f g h 7 7) ∧
  (op a b c d e f g h 7 1) ≠ (op a b c d e f g h 7 2) ∧
  (op a b c d e f g h 7 1) ≠ (op a b c d e f g h 7 3) ∧
  (op a b c d e f g h 7 1) ≠ (op a b c d e f g h 7 4) ∧
  (op a b c d e f g h 7 1) ≠ (op a b c d e f g h 7 5) ∧
  (op a b c d e f g h 7 1) ≠ (op a b c d e f g h 7 6) ∧
  (op a b c d e f g h 7 1) ≠ (op a b c d e f g h 7 7) ∧
  (op a b c d e f g h 7 2) ≠ (op a b c d e f g h 7 3) ∧
  (op a b c d e f g h 7 2) ≠ (op a b c d e f g h 7 4) ∧
  (op a b c d e f g h 7 2) ≠ (op a b c d e f g h 7 5) ∧
  (op a b c d e f g h 7 2) ≠ (op a b c d e f g h 7 6) ∧
  (op a b c d e f g h 7 2) ≠ (op a b c d e f g h 7 7) ∧
  (op a b c d e f g h 7 3) ≠ (op a b c d e f g h 7 4) ∧
  (op a b c d e f g h 7 3) ≠ (op a b c d e f g h 7 5) ∧
  (op a b c d e f g h 7 3) ≠ (op a b c d e f g h 7 6) ∧
  (op a b c d e f g h 7 3) ≠ (op a b c d e f g h 7 7) ∧
  (op a b c d e f g h 7 4) ≠ (op a b c d e f g h 7 5) ∧
  (op a b c d e f g h 7 4) ≠ (op a b c d e f g h 7 6) ∧
  (op a b c d e f g h 7 4) ≠ (op a b c d e f g h 7 7) ∧
  (op a b c d e f g h 7 5) ≠ (op a b c d e f g h 7 6) ∧
  (op a b c d e f g h 7 5) ≠ (op a b c d e f g h 7 7) ∧
  (op a b c d e f g h 7 6) ≠ (op a b c d e f g h 7 7)

end Spectrum.E907Eight
