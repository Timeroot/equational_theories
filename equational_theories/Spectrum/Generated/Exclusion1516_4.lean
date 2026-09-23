import equational_theories.Spectrum.FiniteTableEncoding
import equational_theories.Equations.All

/-! Generated exhaustive refutation, verified by Lean's registered native LRAT checker. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
namespace Spectrum.FiniteExclusion.E1516N4
open FiniteTableEncoding.N4
def test (a0 a1 a2 a3 : BitVec 8) : Prop :=
  (0 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 0 0) (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 0 0))) ∧
  (0 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 1 1) (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 0 1))) ∧
  (0 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 2 2) (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 0 2))) ∧
  (0 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 3 3) (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 0 3))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 0 0) (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 1 0))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 1 1) (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 1 1))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 2 2) (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 1 2))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 3 3) (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 1 3))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 0 0) (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 2 0))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 1 1) (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 2 1))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 2 2) (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 2 2))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 3 3) (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 2 3))) ∧
  (3 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 0 0) (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 3 0))) ∧
  (3 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 1 1) (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 3 1))) ∧
  (3 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 2 2) (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 3 2))) ∧
  (3 : BitVec 2) = (op a0 a1 a2 a3 (op a0 a1 a2 a3 3 3) (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 3 3)))
@[spectrum_native]
theorem refute (a0 a1 a2 a3 : BitVec 8) : ¬ test a0 a1 a2 a3 := by
  unfold test op clip
  bv_decide (config := { timeout := 300, embeddedConstraintSubst := false })
spectrum_assert refute complete
theorem impossible (M : Magma (Fin 4)) (h : @Equation1516 (Fin 4) M) : False := by
  have he := encoded_eq M
  apply refute (rows M 0) (rows M 1) (rows M 2) (rows M 3)
  unfold test
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (bv (0 : Fin 4)) = (encoded M (encoded M (bv (0 : Fin 4)) (bv (0 : Fin 4))) (encoded M (bv (0 : Fin 4)) (encoded M (bv (0 : Fin 4)) (bv (0 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 0 0)
  · change (bv (0 : Fin 4)) = (encoded M (encoded M (bv (1 : Fin 4)) (bv (1 : Fin 4))) (encoded M (bv (0 : Fin 4)) (encoded M (bv (0 : Fin 4)) (bv (1 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 0 1)
  · change (bv (0 : Fin 4)) = (encoded M (encoded M (bv (2 : Fin 4)) (bv (2 : Fin 4))) (encoded M (bv (0 : Fin 4)) (encoded M (bv (0 : Fin 4)) (bv (2 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 0 2)
  · change (bv (0 : Fin 4)) = (encoded M (encoded M (bv (3 : Fin 4)) (bv (3 : Fin 4))) (encoded M (bv (0 : Fin 4)) (encoded M (bv (0 : Fin 4)) (bv (3 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 0 3)
  · change (bv (1 : Fin 4)) = (encoded M (encoded M (bv (0 : Fin 4)) (bv (0 : Fin 4))) (encoded M (bv (1 : Fin 4)) (encoded M (bv (1 : Fin 4)) (bv (0 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 1 0)
  · change (bv (1 : Fin 4)) = (encoded M (encoded M (bv (1 : Fin 4)) (bv (1 : Fin 4))) (encoded M (bv (1 : Fin 4)) (encoded M (bv (1 : Fin 4)) (bv (1 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 1 1)
  · change (bv (1 : Fin 4)) = (encoded M (encoded M (bv (2 : Fin 4)) (bv (2 : Fin 4))) (encoded M (bv (1 : Fin 4)) (encoded M (bv (1 : Fin 4)) (bv (2 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 1 2)
  · change (bv (1 : Fin 4)) = (encoded M (encoded M (bv (3 : Fin 4)) (bv (3 : Fin 4))) (encoded M (bv (1 : Fin 4)) (encoded M (bv (1 : Fin 4)) (bv (3 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 1 3)
  · change (bv (2 : Fin 4)) = (encoded M (encoded M (bv (0 : Fin 4)) (bv (0 : Fin 4))) (encoded M (bv (2 : Fin 4)) (encoded M (bv (2 : Fin 4)) (bv (0 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 2 0)
  · change (bv (2 : Fin 4)) = (encoded M (encoded M (bv (1 : Fin 4)) (bv (1 : Fin 4))) (encoded M (bv (2 : Fin 4)) (encoded M (bv (2 : Fin 4)) (bv (1 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 2 1)
  · change (bv (2 : Fin 4)) = (encoded M (encoded M (bv (2 : Fin 4)) (bv (2 : Fin 4))) (encoded M (bv (2 : Fin 4)) (encoded M (bv (2 : Fin 4)) (bv (2 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 2 2)
  · change (bv (2 : Fin 4)) = (encoded M (encoded M (bv (3 : Fin 4)) (bv (3 : Fin 4))) (encoded M (bv (2 : Fin 4)) (encoded M (bv (2 : Fin 4)) (bv (3 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 2 3)
  · change (bv (3 : Fin 4)) = (encoded M (encoded M (bv (0 : Fin 4)) (bv (0 : Fin 4))) (encoded M (bv (3 : Fin 4)) (encoded M (bv (3 : Fin 4)) (bv (0 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 3 0)
  · change (bv (3 : Fin 4)) = (encoded M (encoded M (bv (1 : Fin 4)) (bv (1 : Fin 4))) (encoded M (bv (3 : Fin 4)) (encoded M (bv (3 : Fin 4)) (bv (1 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 3 1)
  · change (bv (3 : Fin 4)) = (encoded M (encoded M (bv (2 : Fin 4)) (bv (2 : Fin 4))) (encoded M (bv (3 : Fin 4)) (encoded M (bv (3 : Fin 4)) (bv (2 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 3 2)
  · change (bv (3 : Fin 4)) = (encoded M (encoded M (bv (3 : Fin 4)) (bv (3 : Fin 4))) (encoded M (bv (3 : Fin 4)) (encoded M (bv (3 : Fin 4)) (bv (3 : Fin 4)))))
    simp only [he]
    exact congrArg bv (h 3 3)
end Spectrum.FiniteExclusion.E1516N4
theorem Spectrum.not_order_1516_4 : ¬ Law1516.HasModel 4 := by
  rintro ⟨M, hM⟩
  exact Spectrum.FiniteExclusion.E1516N4.impossible M ((@Law1516.models_iff _ M).mp hM)
spectrum_assert Spectrum.not_order_1516_4 complete
