import equational_theories.Spectrum.MendelsohnSix

/-! Exhaustive six-element exclusions. Each bit-vector refutation is checked
by Lean's LRAT checker, and the encoding covers every six-element magma. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
namespace Spectrum.QuasigroupSix
open MendelsohnSix

def op (a b c d e f : BitVec 18) (x y : BitVec 3) : BitVec 3 :=
  clip (((if x = 0 then a else if x = 1 then b else if x = 2 then c
    else if x = 3 then d else if x = 4 then e else f) >>>
    (y.setWidth 18 * 3)).setWidth 3)

def rows (M : Magma (Fin 6)) (x : Fin 6) : BitVec 18 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4) (M.op x 5)
def encoded (M : Magma (Fin 6)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)

theorem encoded_eq (M : Magma (Fin 6)) (x y : Fin 6) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1
      else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3
      else if bv x = 4 then rows M 4 else rows M 5) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3, M.op x 4, M.op x 5] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]

def test115 (a b c d e f : BitVec 18) : Prop :=
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 0 0) 0)) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 0 0) 1)) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 0 0) 2)) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 0 0) 3)) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 0 0) 4)) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 0 0) 5)) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 1 1) 0)) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 1 1) 1)) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 1 1) 2)) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 1 1) 3)) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 1 1) 4)) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 1 1) 5)) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 2 2) 0)) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 2 2) 1)) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 2 2) 2)) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 2 2) 3)) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 2 2) 4)) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 2 2) 5)) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 3 3) 0)) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 3 3) 1)) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 3 3) 2)) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 3 3) 3)) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 3 3) 4)) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 3 3) 5)) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 4 4) 0)) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 4 4) 1)) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 4 4) 2)) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 4 4) 3)) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 4 4) 4)) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 4 4) 5)) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 5 5) 0)) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 5 5) 1)) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 5 5) 2)) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 5 5) 3)) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 5 5) 4)) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 5 5) 5))

@[spectrum_native]
theorem refute115 (a b c d e f : BitVec 18) : ¬ test115 a b c d e f := by
  unfold test115 op clip
  bv_decide (config := { timeout := 60, embeddedConstraintSubst := false })
spectrum_assert refute115 complete

theorem impossible115 (M : Magma (Fin 6)) (h : @Equation115 (Fin 6) M) : False := by
  have he := encoded_eq M
  apply refute115 (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)
  unfold test115
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · change (bv (0 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (bv (0 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 0 0)
  · change (bv (0 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (bv (1 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 0 1)
  · change (bv (0 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (bv (2 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 0 2)
  · change (bv (0 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (bv (3 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 0 3)
  · change (bv (0 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (bv (4 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 0 4)
  · change (bv (0 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (bv (5 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 0 5)
  · change (bv (1 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (bv (0 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 1 0)
  · change (bv (1 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (bv (1 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 1 1)
  · change (bv (1 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (bv (2 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 1 2)
  · change (bv (1 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (bv (3 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 1 3)
  · change (bv (1 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (bv (4 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 1 4)
  · change (bv (1 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (bv (5 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 1 5)
  · change (bv (2 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (bv (0 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 2 0)
  · change (bv (2 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (bv (1 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 2 1)
  · change (bv (2 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (bv (2 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 2 2)
  · change (bv (2 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (bv (3 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 2 3)
  · change (bv (2 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (bv (4 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 2 4)
  · change (bv (2 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (bv (5 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 2 5)
  · change (bv (3 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (bv (0 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 3 0)
  · change (bv (3 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (bv (1 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 3 1)
  · change (bv (3 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (bv (2 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 3 2)
  · change (bv (3 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (bv (3 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 3 3)
  · change (bv (3 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (bv (4 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 3 4)
  · change (bv (3 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (bv (5 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 3 5)
  · change (bv (4 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (bv (0 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 4 0)
  · change (bv (4 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (bv (1 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 4 1)
  · change (bv (4 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (bv (2 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 4 2)
  · change (bv (4 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (bv (3 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 4 3)
  · change (bv (4 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (bv (4 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 4 4)
  · change (bv (4 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (bv (5 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 4 5)
  · change (bv (5 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (bv (0 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 5 0)
  · change (bv (5 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (bv (1 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 5 1)
  · change (bv (5 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (bv (2 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 5 2)
  · change (bv (5 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (bv (3 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 5 3)
  · change (bv (5 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (bv (4 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 5 4)
  · change (bv (5 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (bv (5 : Fin 6))))
    simp only [he]
    exact congrArg bv (h 5 5)

def test481 (a b c d e f : BitVec 18) : Prop :=
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 0 0)))) ∧
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 1 1)))) ∧
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 2 2)))) ∧
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 3 3)))) ∧
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 4 4)))) ∧
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 0 (op a b c d e f 5 5)))) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 0 0)))) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 1 1)))) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 2 2)))) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 3 3)))) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 4 4)))) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 5 5)))) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 0 0)))) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 1 1)))) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 2 2)))) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 3 3)))) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 4 4)))) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 5 5)))) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 0 0)))) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 1 1)))) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 2 2)))) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 3 3)))) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 4 4)))) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 5 5)))) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 0 0)))) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 1 1)))) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 2 2)))) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 3 3)))) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 4 4)))) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 5 5)))) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 0 0)))) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 1 1)))) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 2 2)))) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 3 3)))) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 4 4)))) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 5 5)))) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 0 0)))) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 1 1)))) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 2 2)))) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 3 3)))) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 4 4)))) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 1 (op a b c d e f 0 (op a b c d e f 5 5)))) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 0 0)))) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 1 1)))) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 2 2)))) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 3 3)))) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 4 4)))) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 1 (op a b c d e f 5 5)))) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 0 0)))) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 1 1)))) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 2 2)))) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 3 3)))) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 4 4)))) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 5 5)))) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 0 0)))) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 1 1)))) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 2 2)))) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 3 3)))) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 4 4)))) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 5 5)))) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 0 0)))) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 1 1)))) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 2 2)))) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 3 3)))) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 4 4)))) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 5 5)))) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 0 0)))) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 1 1)))) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 2 2)))) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 3 3)))) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 4 4)))) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 5 5)))) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 0 0)))) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 1 1)))) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 2 2)))) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 3 3)))) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 4 4)))) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 2 (op a b c d e f 0 (op a b c d e f 5 5)))) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 0 0)))) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 1 1)))) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 2 2)))) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 3 3)))) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 4 4)))) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 2 (op a b c d e f 1 (op a b c d e f 5 5)))) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 0 0)))) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 1 1)))) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 2 2)))) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 3 3)))) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 4 4)))) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 2 (op a b c d e f 5 5)))) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 0 0)))) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 1 1)))) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 2 2)))) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 3 3)))) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 4 4)))) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 5 5)))) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 0 0)))) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 1 1)))) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 2 2)))) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 3 3)))) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 4 4)))) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 5 5)))) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 0 0)))) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 1 1)))) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 2 2)))) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 3 3)))) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 4 4)))) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 5 5)))) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 0 0)))) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 1 1)))) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 2 2)))) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 3 3)))) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 4 4)))) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 3 (op a b c d e f 0 (op a b c d e f 5 5)))) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 0 0)))) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 1 1)))) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 2 2)))) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 3 3)))) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 4 4)))) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 3 (op a b c d e f 1 (op a b c d e f 5 5)))) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 0 0)))) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 1 1)))) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 2 2)))) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 3 3)))) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 4 4)))) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 3 (op a b c d e f 2 (op a b c d e f 5 5)))) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 0 0)))) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 1 1)))) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 2 2)))) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 3 3)))) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 4 4)))) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 3 (op a b c d e f 5 5)))) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 0 0)))) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 1 1)))) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 2 2)))) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 3 3)))) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 4 4)))) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 5 5)))) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 0 0)))) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 1 1)))) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 2 2)))) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 3 3)))) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 4 4)))) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 5 5)))) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 0 0)))) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 1 1)))) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 2 2)))) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 3 3)))) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 4 4)))) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 4 (op a b c d e f 0 (op a b c d e f 5 5)))) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 0 0)))) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 1 1)))) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 2 2)))) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 3 3)))) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 4 4)))) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 4 (op a b c d e f 1 (op a b c d e f 5 5)))) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 0 0)))) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 1 1)))) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 2 2)))) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 3 3)))) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 4 4)))) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 4 (op a b c d e f 2 (op a b c d e f 5 5)))) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 0 0)))) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 1 1)))) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 2 2)))) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 3 3)))) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 4 4)))) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 4 (op a b c d e f 3 (op a b c d e f 5 5)))) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 0 0)))) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 1 1)))) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 2 2)))) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 3 3)))) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 4 4)))) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 4 (op a b c d e f 5 5)))) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 0 0)))) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 1 1)))) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 2 2)))) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 3 3)))) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 4 4)))) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 5 5)))) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 0 0)))) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 1 1)))) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 2 2)))) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 3 3)))) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 4 4)))) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f 5 (op a b c d e f 0 (op a b c d e f 5 5)))) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 0 0)))) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 1 1)))) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 2 2)))) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 3 3)))) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 4 4)))) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f 5 (op a b c d e f 1 (op a b c d e f 5 5)))) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 0 0)))) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 1 1)))) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 2 2)))) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 3 3)))) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 4 4)))) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f 5 (op a b c d e f 2 (op a b c d e f 5 5)))) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 0 0)))) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 1 1)))) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 2 2)))) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 3 3)))) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 4 4)))) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f 5 (op a b c d e f 3 (op a b c d e f 5 5)))) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 0 0)))) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 1 1)))) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 2 2)))) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 3 3)))) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 4 4)))) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f 5 (op a b c d e f 4 (op a b c d e f 5 5)))) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 0 0)))) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 1 1)))) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 2 2)))) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 3 3)))) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 4 4)))) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 5 (op a b c d e f 5 5))))

@[spectrum_native]
theorem refute481 (a b c d e f : BitVec 18) : ¬ test481 a b c d e f := by
  unfold test481 op clip
  bv_decide (config := { timeout := 60, embeddedConstraintSubst := false })
spectrum_assert refute481 complete

theorem impossible481 (M : Magma (Fin 6)) (h : @Equation481 (Fin 6) M) : False := by
  have he := encoded_eq M
  apply refute481 (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)
  unfold test481
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · change (bv (0 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 0 0)
  · change (bv (0 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 0 1)
  · change (bv (0 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 0 2)
  · change (bv (0 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 0 3)
  · change (bv (0 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 0 4)
  · change (bv (0 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 0 5)
  · change (bv (0 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 1 0)
  · change (bv (0 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 1 1)
  · change (bv (0 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 1 2)
  · change (bv (0 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 1 3)
  · change (bv (0 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 1 4)
  · change (bv (0 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 1 5)
  · change (bv (0 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 2 0)
  · change (bv (0 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 2 1)
  · change (bv (0 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 2 2)
  · change (bv (0 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 2 3)
  · change (bv (0 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 2 4)
  · change (bv (0 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 2 5)
  · change (bv (0 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 3 0)
  · change (bv (0 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 3 1)
  · change (bv (0 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 3 2)
  · change (bv (0 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 3 3)
  · change (bv (0 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 3 4)
  · change (bv (0 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 3 5)
  · change (bv (0 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 4 0)
  · change (bv (0 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 4 1)
  · change (bv (0 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 4 2)
  · change (bv (0 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 4 3)
  · change (bv (0 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 4 4)
  · change (bv (0 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 4 5)
  · change (bv (0 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 5 0)
  · change (bv (0 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 5 1)
  · change (bv (0 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 5 2)
  · change (bv (0 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 5 3)
  · change (bv (0 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 5 4)
  · change (bv (0 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 0 5 5)
  · change (bv (1 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 0 0)
  · change (bv (1 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 0 1)
  · change (bv (1 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 0 2)
  · change (bv (1 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 0 3)
  · change (bv (1 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 0 4)
  · change (bv (1 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 0 5)
  · change (bv (1 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 1 0)
  · change (bv (1 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 1 1)
  · change (bv (1 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 1 2)
  · change (bv (1 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 1 3)
  · change (bv (1 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 1 4)
  · change (bv (1 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 1 5)
  · change (bv (1 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 2 0)
  · change (bv (1 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 2 1)
  · change (bv (1 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 2 2)
  · change (bv (1 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 2 3)
  · change (bv (1 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 2 4)
  · change (bv (1 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 2 5)
  · change (bv (1 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 3 0)
  · change (bv (1 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 3 1)
  · change (bv (1 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 3 2)
  · change (bv (1 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 3 3)
  · change (bv (1 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 3 4)
  · change (bv (1 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 3 5)
  · change (bv (1 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 4 0)
  · change (bv (1 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 4 1)
  · change (bv (1 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 4 2)
  · change (bv (1 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 4 3)
  · change (bv (1 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 4 4)
  · change (bv (1 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 4 5)
  · change (bv (1 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 5 0)
  · change (bv (1 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 5 1)
  · change (bv (1 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 5 2)
  · change (bv (1 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 5 3)
  · change (bv (1 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 5 4)
  · change (bv (1 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 1 5 5)
  · change (bv (2 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 0 0)
  · change (bv (2 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 0 1)
  · change (bv (2 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 0 2)
  · change (bv (2 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 0 3)
  · change (bv (2 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 0 4)
  · change (bv (2 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 0 5)
  · change (bv (2 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 1 0)
  · change (bv (2 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 1 1)
  · change (bv (2 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 1 2)
  · change (bv (2 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 1 3)
  · change (bv (2 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 1 4)
  · change (bv (2 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 1 5)
  · change (bv (2 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 2 0)
  · change (bv (2 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 2 1)
  · change (bv (2 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 2 2)
  · change (bv (2 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 2 3)
  · change (bv (2 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 2 4)
  · change (bv (2 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 2 5)
  · change (bv (2 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 3 0)
  · change (bv (2 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 3 1)
  · change (bv (2 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 3 2)
  · change (bv (2 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 3 3)
  · change (bv (2 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 3 4)
  · change (bv (2 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 3 5)
  · change (bv (2 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 4 0)
  · change (bv (2 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 4 1)
  · change (bv (2 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 4 2)
  · change (bv (2 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 4 3)
  · change (bv (2 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 4 4)
  · change (bv (2 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 4 5)
  · change (bv (2 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 5 0)
  · change (bv (2 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 5 1)
  · change (bv (2 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 5 2)
  · change (bv (2 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 5 3)
  · change (bv (2 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 5 4)
  · change (bv (2 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 2 5 5)
  · change (bv (3 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 0 0)
  · change (bv (3 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 0 1)
  · change (bv (3 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 0 2)
  · change (bv (3 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 0 3)
  · change (bv (3 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 0 4)
  · change (bv (3 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 0 5)
  · change (bv (3 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 1 0)
  · change (bv (3 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 1 1)
  · change (bv (3 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 1 2)
  · change (bv (3 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 1 3)
  · change (bv (3 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 1 4)
  · change (bv (3 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 1 5)
  · change (bv (3 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 2 0)
  · change (bv (3 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 2 1)
  · change (bv (3 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 2 2)
  · change (bv (3 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 2 3)
  · change (bv (3 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 2 4)
  · change (bv (3 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 2 5)
  · change (bv (3 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 3 0)
  · change (bv (3 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 3 1)
  · change (bv (3 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 3 2)
  · change (bv (3 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 3 3)
  · change (bv (3 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 3 4)
  · change (bv (3 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 3 5)
  · change (bv (3 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 4 0)
  · change (bv (3 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 4 1)
  · change (bv (3 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 4 2)
  · change (bv (3 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 4 3)
  · change (bv (3 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 4 4)
  · change (bv (3 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 4 5)
  · change (bv (3 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 5 0)
  · change (bv (3 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 5 1)
  · change (bv (3 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 5 2)
  · change (bv (3 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 5 3)
  · change (bv (3 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 5 4)
  · change (bv (3 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 3 5 5)
  · change (bv (4 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 0 0)
  · change (bv (4 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 0 1)
  · change (bv (4 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 0 2)
  · change (bv (4 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 0 3)
  · change (bv (4 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 0 4)
  · change (bv (4 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 0 5)
  · change (bv (4 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 1 0)
  · change (bv (4 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 1 1)
  · change (bv (4 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 1 2)
  · change (bv (4 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 1 3)
  · change (bv (4 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 1 4)
  · change (bv (4 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 1 5)
  · change (bv (4 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 2 0)
  · change (bv (4 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 2 1)
  · change (bv (4 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 2 2)
  · change (bv (4 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 2 3)
  · change (bv (4 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 2 4)
  · change (bv (4 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 2 5)
  · change (bv (4 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 3 0)
  · change (bv (4 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 3 1)
  · change (bv (4 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 3 2)
  · change (bv (4 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 3 3)
  · change (bv (4 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 3 4)
  · change (bv (4 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 3 5)
  · change (bv (4 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 4 0)
  · change (bv (4 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 4 1)
  · change (bv (4 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 4 2)
  · change (bv (4 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 4 3)
  · change (bv (4 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 4 4)
  · change (bv (4 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 4 5)
  · change (bv (4 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 5 0)
  · change (bv (4 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 5 1)
  · change (bv (4 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 5 2)
  · change (bv (4 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 5 3)
  · change (bv (4 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 5 4)
  · change (bv (4 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 4 5 5)
  · change (bv (5 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 0 0)
  · change (bv (5 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 0 1)
  · change (bv (5 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 0 2)
  · change (bv (5 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 0 3)
  · change (bv (5 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 0 4)
  · change (bv (5 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 0 5)
  · change (bv (5 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 1 0)
  · change (bv (5 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 1 1)
  · change (bv (5 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 1 2)
  · change (bv (5 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 1 3)
  · change (bv (5 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 1 4)
  · change (bv (5 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 1 5)
  · change (bv (5 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 2 0)
  · change (bv (5 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 2 1)
  · change (bv (5 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 2 2)
  · change (bv (5 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 2 3)
  · change (bv (5 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 2 4)
  · change (bv (5 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 2 5)
  · change (bv (5 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 3 0)
  · change (bv (5 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 3 1)
  · change (bv (5 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 3 2)
  · change (bv (5 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 3 3)
  · change (bv (5 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 3 4)
  · change (bv (5 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 3 5)
  · change (bv (5 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 4 0)
  · change (bv (5 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 4 1)
  · change (bv (5 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 4 2)
  · change (bv (5 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 4 3)
  · change (bv (5 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 4 4)
  · change (bv (5 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 4 5)
  · change (bv (5 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 5 0)
  · change (bv (5 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 5 1)
  · change (bv (5 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 5 2)
  · change (bv (5 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 5 3)
  · change (bv (5 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 5 4)
  · change (bv (5 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))))))
    simp only [he]
    exact congrArg bv (h 5 5 5)

def test873 (a b c d e f : BitVec 18) : Prop :=
  (0 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 0 0) (op a b c d e f 0 0))) ∧
  (0 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 0 0) (op a b c d e f 1 1))) ∧
  (0 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 0 0) (op a b c d e f 2 2))) ∧
  (0 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 0 0) (op a b c d e f 3 3))) ∧
  (0 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 0 0) (op a b c d e f 4 4))) ∧
  (0 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 0 0) (op a b c d e f 5 5))) ∧
  (1 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 1 1) (op a b c d e f 0 0))) ∧
  (1 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 1 1) (op a b c d e f 1 1))) ∧
  (1 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 1 1) (op a b c d e f 2 2))) ∧
  (1 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 1 1) (op a b c d e f 3 3))) ∧
  (1 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 1 1) (op a b c d e f 4 4))) ∧
  (1 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 1 1) (op a b c d e f 5 5))) ∧
  (2 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 2 2) (op a b c d e f 0 0))) ∧
  (2 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 2 2) (op a b c d e f 1 1))) ∧
  (2 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 2 2) (op a b c d e f 2 2))) ∧
  (2 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 2 2) (op a b c d e f 3 3))) ∧
  (2 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 2 2) (op a b c d e f 4 4))) ∧
  (2 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 2 2) (op a b c d e f 5 5))) ∧
  (3 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 3 3) (op a b c d e f 0 0))) ∧
  (3 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 3 3) (op a b c d e f 1 1))) ∧
  (3 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 3 3) (op a b c d e f 2 2))) ∧
  (3 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 3 3) (op a b c d e f 3 3))) ∧
  (3 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 3 3) (op a b c d e f 4 4))) ∧
  (3 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 3 3) (op a b c d e f 5 5))) ∧
  (4 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 4 4) (op a b c d e f 0 0))) ∧
  (4 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 4 4) (op a b c d e f 1 1))) ∧
  (4 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 4 4) (op a b c d e f 2 2))) ∧
  (4 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 4 4) (op a b c d e f 3 3))) ∧
  (4 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 4 4) (op a b c d e f 4 4))) ∧
  (4 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 4 4) (op a b c d e f 5 5))) ∧
  (5 : BitVec 3) = (op a b c d e f 0 (op a b c d e f (op a b c d e f 5 5) (op a b c d e f 0 0))) ∧
  (5 : BitVec 3) = (op a b c d e f 1 (op a b c d e f (op a b c d e f 5 5) (op a b c d e f 1 1))) ∧
  (5 : BitVec 3) = (op a b c d e f 2 (op a b c d e f (op a b c d e f 5 5) (op a b c d e f 2 2))) ∧
  (5 : BitVec 3) = (op a b c d e f 3 (op a b c d e f (op a b c d e f 5 5) (op a b c d e f 3 3))) ∧
  (5 : BitVec 3) = (op a b c d e f 4 (op a b c d e f (op a b c d e f 5 5) (op a b c d e f 4 4))) ∧
  (5 : BitVec 3) = (op a b c d e f 5 (op a b c d e f (op a b c d e f 5 5) (op a b c d e f 5 5)))

@[spectrum_native]
theorem refute873 (a b c d e f : BitVec 18) : ¬ test873 a b c d e f := by
  unfold test873 op clip
  bv_decide (config := { timeout := 60, embeddedConstraintSubst := false })
spectrum_assert refute873 complete

theorem impossible873 (M : Magma (Fin 6)) (h : @Equation873 (Fin 6) M) : False := by
  have he := encoded_eq M
  apply refute873 (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)
  unfold test873
  refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · change (bv (0 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 0)
  · change (bv (0 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 1)
  · change (bv (0 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 2)
  · change (bv (0 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 3)
  · change (bv (0 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 4)
  · change (bv (0 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6))) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 0 5)
  · change (bv (1 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 0)
  · change (bv (1 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 1)
  · change (bv (1 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 2)
  · change (bv (1 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 3)
  · change (bv (1 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 4)
  · change (bv (1 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6))) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 1 5)
  · change (bv (2 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 0)
  · change (bv (2 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 1)
  · change (bv (2 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 2)
  · change (bv (2 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 3)
  · change (bv (2 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 4)
  · change (bv (2 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6))) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 2 5)
  · change (bv (3 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 0)
  · change (bv (3 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 1)
  · change (bv (3 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 2)
  · change (bv (3 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 3)
  · change (bv (3 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 4)
  · change (bv (3 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6))) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 3 5)
  · change (bv (4 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 0)
  · change (bv (4 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 1)
  · change (bv (4 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 2)
  · change (bv (4 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 3)
  · change (bv (4 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 4)
  · change (bv (4 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6))) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 4 5)
  · change (bv (5 : Fin 6)) = (encoded M (bv (0 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (0 : Fin 6)) (bv (0 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 0)
  · change (bv (5 : Fin 6)) = (encoded M (bv (1 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (1 : Fin 6)) (bv (1 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 1)
  · change (bv (5 : Fin 6)) = (encoded M (bv (2 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (2 : Fin 6)) (bv (2 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 2)
  · change (bv (5 : Fin 6)) = (encoded M (bv (3 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (3 : Fin 6)) (bv (3 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 3)
  · change (bv (5 : Fin 6)) = (encoded M (bv (4 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (4 : Fin 6)) (bv (4 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 4)
  · change (bv (5 : Fin 6)) = (encoded M (bv (5 : Fin 6)) (encoded M (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6))) (encoded M (bv (5 : Fin 6)) (bv (5 : Fin 6)))))
    simp only [he]
    exact congrArg bv (h 5 5)

end Spectrum.QuasigroupSix
