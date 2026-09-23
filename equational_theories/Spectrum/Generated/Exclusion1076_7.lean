import equational_theories.Spectrum.FiniteTableEncoding
import equational_theories.Equations.All

/-! Generated exhaustive refutation, verified by Lean's registered native LRAT checker. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
namespace Spectrum.FiniteExclusion.E1076N7
open FiniteTableEncoding.N7
def test (a0 a1 a2 a3 a4 a5 a6 : BitVec 21) : Prop :=
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 0 0)) 0)) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 0 1)) 1)) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 0 2)) 2)) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 0 3)) 3)) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 0 4)) 4)) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 0 5)) 5)) ∧
  (0 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 0 6)) 6)) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 1 0)) 0)) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 1 1)) 1)) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 1 2)) 2)) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 1 3)) 3)) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 1 4)) 4)) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 1 5)) 5)) ∧
  (1 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 1 6)) 6)) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 2 0)) 0)) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 2 1)) 1)) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 2 2)) 2)) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 2 3)) 3)) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 2 4)) 4)) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 2 5)) 5)) ∧
  (2 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 2 6)) 6)) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 3 0)) 0)) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 3 1)) 1)) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 3 2)) 2)) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 3 3)) 3)) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 3 4)) 4)) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 3 5)) 5)) ∧
  (3 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 3 6)) 6)) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 4 0)) 0)) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 4 1)) 1)) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 4 2)) 2)) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 4 3)) 3)) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 4 4)) 4)) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 4 5)) 5)) ∧
  (4 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 4 6)) 6)) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 5 0)) 0)) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 5 1)) 1)) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 5 2)) 2)) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 5 3)) 3)) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 5 4)) 4)) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 5 5)) 5)) ∧
  (5 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 5 6)) 6)) ∧
  (6 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 0 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 6 0)) 0)) ∧
  (6 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 1 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 6 1)) 1)) ∧
  (6 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 2 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 6 2)) 2)) ∧
  (6 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 3 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 6 3)) 3)) ∧
  (6 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 4 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 6 4)) 4)) ∧
  (6 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 5 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 6 5)) 5)) ∧
  (6 : BitVec 3) = (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 (op a0 a1 a2 a3 a4 a5 a6 6 (op a0 a1 a2 a3 a4 a5 a6 6 6)) 6))
@[spectrum_native]
theorem refute (a0 a1 a2 a3 a4 a5 a6 : BitVec 21) : ¬ test a0 a1 a2 a3 a4 a5 a6 := by
  unfold test op clip
  bv_decide (config := { timeout := 300, embeddedConstraintSubst := false })
spectrum_assert refute complete
theorem impossible (M : Magma (Fin 7)) (h : @Equation1076 (Fin 7) M) : False := by
  have he := encoded_eq M
  apply refute (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6)
  unfold test
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (bv (0 : Fin 7)) = (encoded M (bv (0 : Fin 7)) (encoded M (encoded M (bv (0 : Fin 7)) (encoded M (bv (0 : Fin 7)) (bv (0 : Fin 7)))) (bv (0 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 0 0)
  · change (bv (0 : Fin 7)) = (encoded M (bv (1 : Fin 7)) (encoded M (encoded M (bv (0 : Fin 7)) (encoded M (bv (0 : Fin 7)) (bv (1 : Fin 7)))) (bv (1 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 0 1)
  · change (bv (0 : Fin 7)) = (encoded M (bv (2 : Fin 7)) (encoded M (encoded M (bv (0 : Fin 7)) (encoded M (bv (0 : Fin 7)) (bv (2 : Fin 7)))) (bv (2 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 0 2)
  · change (bv (0 : Fin 7)) = (encoded M (bv (3 : Fin 7)) (encoded M (encoded M (bv (0 : Fin 7)) (encoded M (bv (0 : Fin 7)) (bv (3 : Fin 7)))) (bv (3 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 0 3)
  · change (bv (0 : Fin 7)) = (encoded M (bv (4 : Fin 7)) (encoded M (encoded M (bv (0 : Fin 7)) (encoded M (bv (0 : Fin 7)) (bv (4 : Fin 7)))) (bv (4 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 0 4)
  · change (bv (0 : Fin 7)) = (encoded M (bv (5 : Fin 7)) (encoded M (encoded M (bv (0 : Fin 7)) (encoded M (bv (0 : Fin 7)) (bv (5 : Fin 7)))) (bv (5 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 0 5)
  · change (bv (0 : Fin 7)) = (encoded M (bv (6 : Fin 7)) (encoded M (encoded M (bv (0 : Fin 7)) (encoded M (bv (0 : Fin 7)) (bv (6 : Fin 7)))) (bv (6 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 0 6)
  · change (bv (1 : Fin 7)) = (encoded M (bv (0 : Fin 7)) (encoded M (encoded M (bv (1 : Fin 7)) (encoded M (bv (1 : Fin 7)) (bv (0 : Fin 7)))) (bv (0 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 1 0)
  · change (bv (1 : Fin 7)) = (encoded M (bv (1 : Fin 7)) (encoded M (encoded M (bv (1 : Fin 7)) (encoded M (bv (1 : Fin 7)) (bv (1 : Fin 7)))) (bv (1 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 1 1)
  · change (bv (1 : Fin 7)) = (encoded M (bv (2 : Fin 7)) (encoded M (encoded M (bv (1 : Fin 7)) (encoded M (bv (1 : Fin 7)) (bv (2 : Fin 7)))) (bv (2 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 1 2)
  · change (bv (1 : Fin 7)) = (encoded M (bv (3 : Fin 7)) (encoded M (encoded M (bv (1 : Fin 7)) (encoded M (bv (1 : Fin 7)) (bv (3 : Fin 7)))) (bv (3 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 1 3)
  · change (bv (1 : Fin 7)) = (encoded M (bv (4 : Fin 7)) (encoded M (encoded M (bv (1 : Fin 7)) (encoded M (bv (1 : Fin 7)) (bv (4 : Fin 7)))) (bv (4 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 1 4)
  · change (bv (1 : Fin 7)) = (encoded M (bv (5 : Fin 7)) (encoded M (encoded M (bv (1 : Fin 7)) (encoded M (bv (1 : Fin 7)) (bv (5 : Fin 7)))) (bv (5 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 1 5)
  · change (bv (1 : Fin 7)) = (encoded M (bv (6 : Fin 7)) (encoded M (encoded M (bv (1 : Fin 7)) (encoded M (bv (1 : Fin 7)) (bv (6 : Fin 7)))) (bv (6 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 1 6)
  · change (bv (2 : Fin 7)) = (encoded M (bv (0 : Fin 7)) (encoded M (encoded M (bv (2 : Fin 7)) (encoded M (bv (2 : Fin 7)) (bv (0 : Fin 7)))) (bv (0 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 2 0)
  · change (bv (2 : Fin 7)) = (encoded M (bv (1 : Fin 7)) (encoded M (encoded M (bv (2 : Fin 7)) (encoded M (bv (2 : Fin 7)) (bv (1 : Fin 7)))) (bv (1 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 2 1)
  · change (bv (2 : Fin 7)) = (encoded M (bv (2 : Fin 7)) (encoded M (encoded M (bv (2 : Fin 7)) (encoded M (bv (2 : Fin 7)) (bv (2 : Fin 7)))) (bv (2 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 2 2)
  · change (bv (2 : Fin 7)) = (encoded M (bv (3 : Fin 7)) (encoded M (encoded M (bv (2 : Fin 7)) (encoded M (bv (2 : Fin 7)) (bv (3 : Fin 7)))) (bv (3 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 2 3)
  · change (bv (2 : Fin 7)) = (encoded M (bv (4 : Fin 7)) (encoded M (encoded M (bv (2 : Fin 7)) (encoded M (bv (2 : Fin 7)) (bv (4 : Fin 7)))) (bv (4 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 2 4)
  · change (bv (2 : Fin 7)) = (encoded M (bv (5 : Fin 7)) (encoded M (encoded M (bv (2 : Fin 7)) (encoded M (bv (2 : Fin 7)) (bv (5 : Fin 7)))) (bv (5 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 2 5)
  · change (bv (2 : Fin 7)) = (encoded M (bv (6 : Fin 7)) (encoded M (encoded M (bv (2 : Fin 7)) (encoded M (bv (2 : Fin 7)) (bv (6 : Fin 7)))) (bv (6 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 2 6)
  · change (bv (3 : Fin 7)) = (encoded M (bv (0 : Fin 7)) (encoded M (encoded M (bv (3 : Fin 7)) (encoded M (bv (3 : Fin 7)) (bv (0 : Fin 7)))) (bv (0 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 3 0)
  · change (bv (3 : Fin 7)) = (encoded M (bv (1 : Fin 7)) (encoded M (encoded M (bv (3 : Fin 7)) (encoded M (bv (3 : Fin 7)) (bv (1 : Fin 7)))) (bv (1 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 3 1)
  · change (bv (3 : Fin 7)) = (encoded M (bv (2 : Fin 7)) (encoded M (encoded M (bv (3 : Fin 7)) (encoded M (bv (3 : Fin 7)) (bv (2 : Fin 7)))) (bv (2 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 3 2)
  · change (bv (3 : Fin 7)) = (encoded M (bv (3 : Fin 7)) (encoded M (encoded M (bv (3 : Fin 7)) (encoded M (bv (3 : Fin 7)) (bv (3 : Fin 7)))) (bv (3 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 3 3)
  · change (bv (3 : Fin 7)) = (encoded M (bv (4 : Fin 7)) (encoded M (encoded M (bv (3 : Fin 7)) (encoded M (bv (3 : Fin 7)) (bv (4 : Fin 7)))) (bv (4 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 3 4)
  · change (bv (3 : Fin 7)) = (encoded M (bv (5 : Fin 7)) (encoded M (encoded M (bv (3 : Fin 7)) (encoded M (bv (3 : Fin 7)) (bv (5 : Fin 7)))) (bv (5 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 3 5)
  · change (bv (3 : Fin 7)) = (encoded M (bv (6 : Fin 7)) (encoded M (encoded M (bv (3 : Fin 7)) (encoded M (bv (3 : Fin 7)) (bv (6 : Fin 7)))) (bv (6 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 3 6)
  · change (bv (4 : Fin 7)) = (encoded M (bv (0 : Fin 7)) (encoded M (encoded M (bv (4 : Fin 7)) (encoded M (bv (4 : Fin 7)) (bv (0 : Fin 7)))) (bv (0 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 4 0)
  · change (bv (4 : Fin 7)) = (encoded M (bv (1 : Fin 7)) (encoded M (encoded M (bv (4 : Fin 7)) (encoded M (bv (4 : Fin 7)) (bv (1 : Fin 7)))) (bv (1 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 4 1)
  · change (bv (4 : Fin 7)) = (encoded M (bv (2 : Fin 7)) (encoded M (encoded M (bv (4 : Fin 7)) (encoded M (bv (4 : Fin 7)) (bv (2 : Fin 7)))) (bv (2 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 4 2)
  · change (bv (4 : Fin 7)) = (encoded M (bv (3 : Fin 7)) (encoded M (encoded M (bv (4 : Fin 7)) (encoded M (bv (4 : Fin 7)) (bv (3 : Fin 7)))) (bv (3 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 4 3)
  · change (bv (4 : Fin 7)) = (encoded M (bv (4 : Fin 7)) (encoded M (encoded M (bv (4 : Fin 7)) (encoded M (bv (4 : Fin 7)) (bv (4 : Fin 7)))) (bv (4 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 4 4)
  · change (bv (4 : Fin 7)) = (encoded M (bv (5 : Fin 7)) (encoded M (encoded M (bv (4 : Fin 7)) (encoded M (bv (4 : Fin 7)) (bv (5 : Fin 7)))) (bv (5 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 4 5)
  · change (bv (4 : Fin 7)) = (encoded M (bv (6 : Fin 7)) (encoded M (encoded M (bv (4 : Fin 7)) (encoded M (bv (4 : Fin 7)) (bv (6 : Fin 7)))) (bv (6 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 4 6)
  · change (bv (5 : Fin 7)) = (encoded M (bv (0 : Fin 7)) (encoded M (encoded M (bv (5 : Fin 7)) (encoded M (bv (5 : Fin 7)) (bv (0 : Fin 7)))) (bv (0 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 5 0)
  · change (bv (5 : Fin 7)) = (encoded M (bv (1 : Fin 7)) (encoded M (encoded M (bv (5 : Fin 7)) (encoded M (bv (5 : Fin 7)) (bv (1 : Fin 7)))) (bv (1 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 5 1)
  · change (bv (5 : Fin 7)) = (encoded M (bv (2 : Fin 7)) (encoded M (encoded M (bv (5 : Fin 7)) (encoded M (bv (5 : Fin 7)) (bv (2 : Fin 7)))) (bv (2 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 5 2)
  · change (bv (5 : Fin 7)) = (encoded M (bv (3 : Fin 7)) (encoded M (encoded M (bv (5 : Fin 7)) (encoded M (bv (5 : Fin 7)) (bv (3 : Fin 7)))) (bv (3 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 5 3)
  · change (bv (5 : Fin 7)) = (encoded M (bv (4 : Fin 7)) (encoded M (encoded M (bv (5 : Fin 7)) (encoded M (bv (5 : Fin 7)) (bv (4 : Fin 7)))) (bv (4 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 5 4)
  · change (bv (5 : Fin 7)) = (encoded M (bv (5 : Fin 7)) (encoded M (encoded M (bv (5 : Fin 7)) (encoded M (bv (5 : Fin 7)) (bv (5 : Fin 7)))) (bv (5 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 5 5)
  · change (bv (5 : Fin 7)) = (encoded M (bv (6 : Fin 7)) (encoded M (encoded M (bv (5 : Fin 7)) (encoded M (bv (5 : Fin 7)) (bv (6 : Fin 7)))) (bv (6 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 5 6)
  · change (bv (6 : Fin 7)) = (encoded M (bv (0 : Fin 7)) (encoded M (encoded M (bv (6 : Fin 7)) (encoded M (bv (6 : Fin 7)) (bv (0 : Fin 7)))) (bv (0 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 6 0)
  · change (bv (6 : Fin 7)) = (encoded M (bv (1 : Fin 7)) (encoded M (encoded M (bv (6 : Fin 7)) (encoded M (bv (6 : Fin 7)) (bv (1 : Fin 7)))) (bv (1 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 6 1)
  · change (bv (6 : Fin 7)) = (encoded M (bv (2 : Fin 7)) (encoded M (encoded M (bv (6 : Fin 7)) (encoded M (bv (6 : Fin 7)) (bv (2 : Fin 7)))) (bv (2 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 6 2)
  · change (bv (6 : Fin 7)) = (encoded M (bv (3 : Fin 7)) (encoded M (encoded M (bv (6 : Fin 7)) (encoded M (bv (6 : Fin 7)) (bv (3 : Fin 7)))) (bv (3 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 6 3)
  · change (bv (6 : Fin 7)) = (encoded M (bv (4 : Fin 7)) (encoded M (encoded M (bv (6 : Fin 7)) (encoded M (bv (6 : Fin 7)) (bv (4 : Fin 7)))) (bv (4 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 6 4)
  · change (bv (6 : Fin 7)) = (encoded M (bv (5 : Fin 7)) (encoded M (encoded M (bv (6 : Fin 7)) (encoded M (bv (6 : Fin 7)) (bv (5 : Fin 7)))) (bv (5 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 6 5)
  · change (bv (6 : Fin 7)) = (encoded M (bv (6 : Fin 7)) (encoded M (encoded M (bv (6 : Fin 7)) (encoded M (bv (6 : Fin 7)) (bv (6 : Fin 7)))) (bv (6 : Fin 7))))
    simp only [he]
    exact congrArg bv (h 6 6)
end Spectrum.FiniteExclusion.E1076N7
theorem Spectrum.not_order_1076_7 : ¬ Law1076.HasModel 7 := by
  rintro ⟨M, hM⟩
  exact Spectrum.FiniteExclusion.E1076N7.impossible M ((@Law1076.models_iff _ M).mp hM)
spectrum_assert Spectrum.not_order_1076_7 complete
