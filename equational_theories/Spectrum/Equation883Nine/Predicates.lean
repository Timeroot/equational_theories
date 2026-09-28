import equational_theories.Spectrum.Equation883Nine.Table

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

namespace Spectrum.E883Nine

def testLaw (a b c d e f g h i : BitVec 36) : Prop :=
  (0 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 0 0) (op a b c d e f g h i 0 0))) ∧
  (0 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 0 1) (op a b c d e f g h i 1 1))) ∧
  (0 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 0 2) (op a b c d e f g h i 2 2))) ∧
  (0 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 0 3) (op a b c d e f g h i 3 3))) ∧
  (0 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 0 4) (op a b c d e f g h i 4 4))) ∧
  (0 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 0 5) (op a b c d e f g h i 5 5))) ∧
  (0 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 0 6) (op a b c d e f g h i 6 6))) ∧
  (0 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 0 7) (op a b c d e f g h i 7 7))) ∧
  (0 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 0 8) (op a b c d e f g h i 8 8))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 1 0) (op a b c d e f g h i 0 0))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 1 1) (op a b c d e f g h i 1 1))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 1 2) (op a b c d e f g h i 2 2))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 1 3) (op a b c d e f g h i 3 3))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 1 4) (op a b c d e f g h i 4 4))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 1 5) (op a b c d e f g h i 5 5))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 1 6) (op a b c d e f g h i 6 6))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 1 7) (op a b c d e f g h i 7 7))) ∧
  (1 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 1 8) (op a b c d e f g h i 8 8))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 2 0) (op a b c d e f g h i 0 0))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 2 1) (op a b c d e f g h i 1 1))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 2 2) (op a b c d e f g h i 2 2))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 2 3) (op a b c d e f g h i 3 3))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 2 4) (op a b c d e f g h i 4 4))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 2 5) (op a b c d e f g h i 5 5))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 2 6) (op a b c d e f g h i 6 6))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 2 7) (op a b c d e f g h i 7 7))) ∧
  (2 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 2 8) (op a b c d e f g h i 8 8))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 3 0) (op a b c d e f g h i 0 0))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 3 1) (op a b c d e f g h i 1 1))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 3 2) (op a b c d e f g h i 2 2))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 3 3) (op a b c d e f g h i 3 3))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 3 4) (op a b c d e f g h i 4 4))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 3 5) (op a b c d e f g h i 5 5))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 3 6) (op a b c d e f g h i 6 6))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 3 7) (op a b c d e f g h i 7 7))) ∧
  (3 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 3 8) (op a b c d e f g h i 8 8))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 4 0) (op a b c d e f g h i 0 0))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 4 1) (op a b c d e f g h i 1 1))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 4 2) (op a b c d e f g h i 2 2))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 4 3) (op a b c d e f g h i 3 3))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 4 4) (op a b c d e f g h i 4 4))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 4 5) (op a b c d e f g h i 5 5))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 4 6) (op a b c d e f g h i 6 6))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 4 7) (op a b c d e f g h i 7 7))) ∧
  (4 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 4 8) (op a b c d e f g h i 8 8))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 5 0) (op a b c d e f g h i 0 0))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 5 1) (op a b c d e f g h i 1 1))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 5 2) (op a b c d e f g h i 2 2))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 5 3) (op a b c d e f g h i 3 3))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 5 4) (op a b c d e f g h i 4 4))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 5 5) (op a b c d e f g h i 5 5))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 5 6) (op a b c d e f g h i 6 6))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 5 7) (op a b c d e f g h i 7 7))) ∧
  (5 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 5 8) (op a b c d e f g h i 8 8))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 6 0) (op a b c d e f g h i 0 0))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 6 1) (op a b c d e f g h i 1 1))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 6 2) (op a b c d e f g h i 2 2))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 6 3) (op a b c d e f g h i 3 3))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 6 4) (op a b c d e f g h i 4 4))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 6 5) (op a b c d e f g h i 5 5))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 6 6) (op a b c d e f g h i 6 6))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 6 7) (op a b c d e f g h i 7 7))) ∧
  (6 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 6 8) (op a b c d e f g h i 8 8))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 7 0) (op a b c d e f g h i 0 0))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 7 1) (op a b c d e f g h i 1 1))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 7 2) (op a b c d e f g h i 2 2))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 7 3) (op a b c d e f g h i 3 3))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 7 4) (op a b c d e f g h i 4 4))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 7 5) (op a b c d e f g h i 5 5))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 7 6) (op a b c d e f g h i 6 6))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 7 7) (op a b c d e f g h i 7 7))) ∧
  (7 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 7 8) (op a b c d e f g h i 8 8))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 0 (op a b c d e f g h i (op a b c d e f g h i 8 0) (op a b c d e f g h i 0 0))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 1 (op a b c d e f g h i (op a b c d e f g h i 8 1) (op a b c d e f g h i 1 1))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 2 (op a b c d e f g h i (op a b c d e f g h i 8 2) (op a b c d e f g h i 2 2))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 3 (op a b c d e f g h i (op a b c d e f g h i 8 3) (op a b c d e f g h i 3 3))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 4 (op a b c d e f g h i (op a b c d e f g h i 8 4) (op a b c d e f g h i 4 4))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 5 (op a b c d e f g h i (op a b c d e f g h i 8 5) (op a b c d e f g h i 5 5))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 6 (op a b c d e f g h i (op a b c d e f g h i 8 6) (op a b c d e f g h i 6 6))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 7 (op a b c d e f g h i (op a b c d e f g h i 8 7) (op a b c d e f g h i 7 7))) ∧
  (8 : BitVec 4) = (op a b c d e f g h i 8 (op a b c d e f g h i (op a b c d e f g h i 8 8) (op a b c d e f g h i 8 8)))

def testNonidentity (a b c d e f g h i : BitVec 36) : Prop :=
  (op a b c d e f g h i 0 0) ≠ 0 ∨
  (op a b c d e f g h i 0 1) ≠ 1 ∨
  (op a b c d e f g h i 0 2) ≠ 2 ∨
  (op a b c d e f g h i 0 3) ≠ 3 ∨
  (op a b c d e f g h i 0 4) ≠ 4 ∨
  (op a b c d e f g h i 0 5) ≠ 5 ∨
  (op a b c d e f g h i 0 6) ≠ 6 ∨
  (op a b c d e f g h i 0 7) ≠ 7 ∨
  (op a b c d e f g h i 0 8) ≠ 8

def testLatin (a b c d e f g h i : BitVec 36) : Prop :=
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 0 1) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 0 2) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 0 3) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 0 4) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 0 5) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 0 6) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 0 7) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 0 8) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 0 2) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 0 3) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 0 4) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 0 5) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 0 6) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 0 7) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 0 8) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 0 3) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 0 4) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 0 5) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 0 6) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 0 7) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 0 8) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 0 4) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 0 5) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 0 6) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 0 7) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 0 8) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 0 5) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 0 6) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 0 7) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 0 8) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 0 6) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 0 7) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 0 8) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 0 7) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 0 8) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 0 8) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 1 1) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 1 2) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 1 3) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 1 4) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 1 5) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 1 6) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 1 7) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 1 2) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 1 3) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 1 4) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 1 5) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 1 6) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 1 7) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 1 3) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 1 4) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 1 5) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 1 6) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 1 7) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 1 4) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 1 5) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 1 6) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 1 7) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 1 5) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 1 6) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 1 7) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 1 6) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 1 7) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 1 7) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 1 7) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 2 1) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 2 2) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 2 3) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 2 4) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 2 5) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 2 6) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 2 2) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 2 3) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 2 4) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 2 5) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 2 6) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 2 3) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 2 4) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 2 5) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 2 6) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 2 4) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 2 5) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 2 6) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 2 5) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 2 6) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 2 6) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 2 6) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 2 6) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 2 7) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 3 1) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 3 2) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 3 3) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 3 4) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 3 5) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 3 2) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 3 3) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 3 4) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 3 5) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 3 3) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 3 4) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 3 5) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 3 4) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 3 5) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 3 5) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 3 5) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 3 5) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 3 5) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 3 6) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 3 6) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 3 7) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 4 1) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 4 2) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 4 3) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 4 4) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 4 2) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 4 3) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 4 4) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 4 3) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 4 4) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 4 4) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 4 4) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 4 4) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 4 4) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 4 4) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 4 5) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 4 5) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 4 5) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 4 6) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 4 6) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 4 7) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 5 1) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 5 2) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 5 3) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 5 2) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 5 3) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 5 3) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 5 3) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 5 3) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 5 3) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 5 3) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 5 3) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 5 4) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 5 4) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 5 4) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 5 4) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 5 5) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 5 5) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 5 5) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 5 6) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 5 6) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 5 7) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 6 1) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 6 2) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 6 2) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 6 2) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 6 2) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 6 2) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 6 2) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 6 2) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 6 2) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 6 3) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 6 3) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 6 3) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 6 3) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 6 3) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 6 4) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 6 4) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 6 4) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 6 4) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 6 5) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 6 5) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 6 5) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 6 6) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 6 6) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 6 7) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 7 1) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 7 1) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 7 1) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 7 1) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 7 1) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 7 1) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 7 1) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 7 1) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 7 2) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 7 2) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 7 2) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 7 2) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 7 2) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 7 2) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 7 3) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 7 3) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 7 3) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 7 3) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 7 3) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 7 4) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 7 4) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 7 4) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 7 4) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 7 5) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 7 5) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 7 5) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 7 6) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 7 6) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 7 7) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 8 0) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 8 0) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 8 0) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 8 0) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 8 0) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 8 0) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 8 0) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 8 0) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 8 1) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 8 1) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 8 1) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 8 1) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 8 1) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 8 1) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 8 1) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 8 2) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 8 2) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 8 2) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 8 2) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 8 2) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 8 2) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 8 3) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 8 3) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 8 3) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 8 3) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 8 3) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 8 4) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 8 4) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 8 4) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 8 4) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 8 5) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 8 5) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 8 5) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 8 6) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 8 6) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 8 7) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 1 0) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 2 0) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 3 0) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 4 0) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 5 0) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 6 0) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 7 0) ∧
  (op a b c d e f g h i 0 0) ≠ (op a b c d e f g h i 8 0) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 2 0) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 3 0) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 4 0) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 5 0) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 6 0) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 7 0) ∧
  (op a b c d e f g h i 1 0) ≠ (op a b c d e f g h i 8 0) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 3 0) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 4 0) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 5 0) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 6 0) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 7 0) ∧
  (op a b c d e f g h i 2 0) ≠ (op a b c d e f g h i 8 0) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 4 0) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 5 0) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 6 0) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 7 0) ∧
  (op a b c d e f g h i 3 0) ≠ (op a b c d e f g h i 8 0) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 5 0) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 6 0) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 7 0) ∧
  (op a b c d e f g h i 4 0) ≠ (op a b c d e f g h i 8 0) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 6 0) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 7 0) ∧
  (op a b c d e f g h i 5 0) ≠ (op a b c d e f g h i 8 0) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 7 0) ∧
  (op a b c d e f g h i 6 0) ≠ (op a b c d e f g h i 8 0) ∧
  (op a b c d e f g h i 7 0) ≠ (op a b c d e f g h i 8 0) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 1 1) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 2 1) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 3 1) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 4 1) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 5 1) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 6 1) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 7 1) ∧
  (op a b c d e f g h i 0 1) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 2 1) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 3 1) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 4 1) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 5 1) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 6 1) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 7 1) ∧
  (op a b c d e f g h i 1 1) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 3 1) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 4 1) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 5 1) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 6 1) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 7 1) ∧
  (op a b c d e f g h i 2 1) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 4 1) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 5 1) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 6 1) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 7 1) ∧
  (op a b c d e f g h i 3 1) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 5 1) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 6 1) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 7 1) ∧
  (op a b c d e f g h i 4 1) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 6 1) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 7 1) ∧
  (op a b c d e f g h i 5 1) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 7 1) ∧
  (op a b c d e f g h i 6 1) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 7 1) ≠ (op a b c d e f g h i 8 1) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 1 2) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 2 2) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 3 2) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 4 2) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 5 2) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 6 2) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 0 2) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 2 2) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 3 2) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 4 2) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 5 2) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 6 2) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 1 2) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 3 2) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 4 2) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 5 2) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 6 2) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 2 2) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 4 2) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 5 2) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 6 2) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 3 2) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 5 2) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 6 2) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 4 2) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 6 2) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 5 2) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 6 2) ≠ (op a b c d e f g h i 7 2) ∧
  (op a b c d e f g h i 6 2) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 7 2) ≠ (op a b c d e f g h i 8 2) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 1 3) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 2 3) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 3 3) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 4 3) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 5 3) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 0 3) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 2 3) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 3 3) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 4 3) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 5 3) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 1 3) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 3 3) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 4 3) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 5 3) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 2 3) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 4 3) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 5 3) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 3 3) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 5 3) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 4 3) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 5 3) ≠ (op a b c d e f g h i 6 3) ∧
  (op a b c d e f g h i 5 3) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 5 3) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 6 3) ≠ (op a b c d e f g h i 7 3) ∧
  (op a b c d e f g h i 6 3) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 7 3) ≠ (op a b c d e f g h i 8 3) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 1 4) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 2 4) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 3 4) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 4 4) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 0 4) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 2 4) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 3 4) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 4 4) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 1 4) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 3 4) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 4 4) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 2 4) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 4 4) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 3 4) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 4 4) ≠ (op a b c d e f g h i 5 4) ∧
  (op a b c d e f g h i 4 4) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 4 4) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 4 4) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 5 4) ≠ (op a b c d e f g h i 6 4) ∧
  (op a b c d e f g h i 5 4) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 5 4) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 6 4) ≠ (op a b c d e f g h i 7 4) ∧
  (op a b c d e f g h i 6 4) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 7 4) ≠ (op a b c d e f g h i 8 4) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 1 5) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 2 5) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 3 5) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 0 5) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 2 5) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 3 5) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 1 5) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 3 5) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 2 5) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 3 5) ≠ (op a b c d e f g h i 4 5) ∧
  (op a b c d e f g h i 3 5) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 3 5) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 3 5) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 3 5) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 4 5) ≠ (op a b c d e f g h i 5 5) ∧
  (op a b c d e f g h i 4 5) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 4 5) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 4 5) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 5 5) ≠ (op a b c d e f g h i 6 5) ∧
  (op a b c d e f g h i 5 5) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 5 5) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 6 5) ≠ (op a b c d e f g h i 7 5) ∧
  (op a b c d e f g h i 6 5) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 7 5) ≠ (op a b c d e f g h i 8 5) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 1 6) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 2 6) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 0 6) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 2 6) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 1 6) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 2 6) ≠ (op a b c d e f g h i 3 6) ∧
  (op a b c d e f g h i 2 6) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 2 6) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 2 6) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 2 6) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 2 6) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 3 6) ≠ (op a b c d e f g h i 4 6) ∧
  (op a b c d e f g h i 3 6) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 3 6) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 3 6) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 3 6) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 4 6) ≠ (op a b c d e f g h i 5 6) ∧
  (op a b c d e f g h i 4 6) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 4 6) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 4 6) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 5 6) ≠ (op a b c d e f g h i 6 6) ∧
  (op a b c d e f g h i 5 6) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 5 6) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 6 6) ≠ (op a b c d e f g h i 7 6) ∧
  (op a b c d e f g h i 6 6) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 7 6) ≠ (op a b c d e f g h i 8 6) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 1 7) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 0 7) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 1 7) ≠ (op a b c d e f g h i 2 7) ∧
  (op a b c d e f g h i 1 7) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 1 7) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 1 7) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 1 7) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 1 7) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 1 7) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 2 7) ≠ (op a b c d e f g h i 3 7) ∧
  (op a b c d e f g h i 2 7) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 2 7) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 2 7) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 2 7) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 2 7) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 3 7) ≠ (op a b c d e f g h i 4 7) ∧
  (op a b c d e f g h i 3 7) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 3 7) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 3 7) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 3 7) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 4 7) ≠ (op a b c d e f g h i 5 7) ∧
  (op a b c d e f g h i 4 7) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 4 7) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 4 7) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 5 7) ≠ (op a b c d e f g h i 6 7) ∧
  (op a b c d e f g h i 5 7) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 5 7) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 6 7) ≠ (op a b c d e f g h i 7 7) ∧
  (op a b c d e f g h i 6 7) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 7 7) ≠ (op a b c d e f g h i 8 7) ∧
  (op a b c d e f g h i 0 8) ≠ (op a b c d e f g h i 1 8) ∧
  (op a b c d e f g h i 0 8) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 0 8) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 0 8) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 0 8) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 0 8) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 0 8) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 0 8) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 1 8) ≠ (op a b c d e f g h i 2 8) ∧
  (op a b c d e f g h i 1 8) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 1 8) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 1 8) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 1 8) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 1 8) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 1 8) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 2 8) ≠ (op a b c d e f g h i 3 8) ∧
  (op a b c d e f g h i 2 8) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 2 8) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 2 8) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 2 8) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 2 8) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 3 8) ≠ (op a b c d e f g h i 4 8) ∧
  (op a b c d e f g h i 3 8) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 3 8) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 3 8) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 3 8) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 4 8) ≠ (op a b c d e f g h i 5 8) ∧
  (op a b c d e f g h i 4 8) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 4 8) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 4 8) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 5 8) ≠ (op a b c d e f g h i 6 8) ∧
  (op a b c d e f g h i 5 8) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 5 8) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 6 8) ≠ (op a b c d e f g h i 7 8) ∧
  (op a b c d e f g h i 6 8) ≠ (op a b c d e f g h i 8 8) ∧
  (op a b c d e f g h i 7 8) ≠ (op a b c d e f g h i 8 8)

end Spectrum.E883Nine
