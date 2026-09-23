import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status
import Lean.Elab.Tactic.BVDecide
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! Generated finite table encodings. Each encoding represents every magma of the indicated size. -/
namespace Spectrum.FiniteTableEncoding
namespace N4
def bv (x : Fin 4) : BitVec 2 := BitVec.ofFin (x.castLE (by decide : 4 ≤ 4))
def clip (x : BitVec 2) : BitVec 2 := x
@[simp] theorem clip_bv (x : Fin 4) : clip (bv x) = bv x := by fin_cases x <;> decide
def pack (a0 a1 a2 a3 : Fin 4) : BitVec 8 := bv a3 ++ bv a2 ++ bv a1 ++ bv a0
@[spectrum_native]
theorem row_correct (a0 a1 a2 a3 y : Fin 4) :
    ((pack a0 a1 a2 a3 >>> ((bv y).setWidth 8 * 2)).setWidth 2) =
      bv (![a0, a1, a2, a3] y) := by
  fin_cases y
  · change (((bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (0 : BitVec 8)).setWidth 2) = bv a0
    bv_decide
  · change (((bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (2 : BitVec 8)).setWidth 2) = bv a1
    bv_decide
  · change (((bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (4 : BitVec 8)).setWidth 2) = bv a2
    bv_decide
  · change (((bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (6 : BitVec 8)).setWidth 2) = bv a3
    bv_decide
def op (a0 a1 a2 a3 : BitVec 8) (x y : BitVec 2) : BitVec 2 :=
  clip (((if x = 0 then a0 else if x = 1 then a1 else if x = 2 then a2 else a3) >>> (y.setWidth 8 * 2)).setWidth 2)
def rows (M : Magma (Fin 4)) (x : Fin 4) : BitVec 8 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3)
def encoded (M : Magma (Fin 4)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3)
theorem encoded_eq (M : Magma (Fin 4)) (x y : Fin 4) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1 else if bv x = 2 then rows M 2 else rows M 3) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]
end N4

namespace N5
def bv (x : Fin 5) : BitVec 3 := BitVec.ofFin (x.castLE (by decide : 5 ≤ 8))
def clip (x : BitVec 3) : BitVec 3 := if x < 5 then x else 0
@[simp] theorem clip_bv (x : Fin 5) : clip (bv x) = bv x := by fin_cases x <;> decide
def pack (a0 a1 a2 a3 a4 : Fin 5) : BitVec 15 := bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0
@[spectrum_native]
theorem row_correct (a0 a1 a2 a3 a4 y : Fin 5) :
    ((pack a0 a1 a2 a3 a4 >>> ((bv y).setWidth 15 * 3)).setWidth 3) =
      bv (![a0, a1, a2, a3, a4] y) := by
  fin_cases y
  · change (((bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (0 : BitVec 15)).setWidth 3) = bv a0
    bv_decide
  · change (((bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (3 : BitVec 15)).setWidth 3) = bv a1
    bv_decide
  · change (((bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (6 : BitVec 15)).setWidth 3) = bv a2
    bv_decide
  · change (((bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (9 : BitVec 15)).setWidth 3) = bv a3
    bv_decide
  · change (((bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (12 : BitVec 15)).setWidth 3) = bv a4
    bv_decide
def op (a0 a1 a2 a3 a4 : BitVec 15) (x y : BitVec 3) : BitVec 3 :=
  clip (((if x = 0 then a0 else if x = 1 then a1 else if x = 2 then a2 else if x = 3 then a3 else a4) >>> (y.setWidth 15 * 3)).setWidth 3)
def rows (M : Magma (Fin 5)) (x : Fin 5) : BitVec 15 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4)
def encoded (M : Magma (Fin 5)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4)
theorem encoded_eq (M : Magma (Fin 5)) (x y : Fin 5) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1 else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3 else rows M 4) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3, M.op x 4] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]
end N5

namespace N6
def bv (x : Fin 6) : BitVec 3 := BitVec.ofFin (x.castLE (by decide : 6 ≤ 8))
def clip (x : BitVec 3) : BitVec 3 := if x < 6 then x else 0
@[simp] theorem clip_bv (x : Fin 6) : clip (bv x) = bv x := by fin_cases x <;> decide
def pack (a0 a1 a2 a3 a4 a5 : Fin 6) : BitVec 18 := bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0
@[spectrum_native]
theorem row_correct (a0 a1 a2 a3 a4 a5 y : Fin 6) :
    ((pack a0 a1 a2 a3 a4 a5 >>> ((bv y).setWidth 18 * 3)).setWidth 3) =
      bv (![a0, a1, a2, a3, a4, a5] y) := by
  fin_cases y
  · change (((bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (0 : BitVec 18)).setWidth 3) = bv a0
    bv_decide
  · change (((bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (3 : BitVec 18)).setWidth 3) = bv a1
    bv_decide
  · change (((bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (6 : BitVec 18)).setWidth 3) = bv a2
    bv_decide
  · change (((bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (9 : BitVec 18)).setWidth 3) = bv a3
    bv_decide
  · change (((bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (12 : BitVec 18)).setWidth 3) = bv a4
    bv_decide
  · change (((bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (15 : BitVec 18)).setWidth 3) = bv a5
    bv_decide
def op (a0 a1 a2 a3 a4 a5 : BitVec 18) (x y : BitVec 3) : BitVec 3 :=
  clip (((if x = 0 then a0 else if x = 1 then a1 else if x = 2 then a2 else if x = 3 then a3 else if x = 4 then a4 else a5) >>> (y.setWidth 18 * 3)).setWidth 3)
def rows (M : Magma (Fin 6)) (x : Fin 6) : BitVec 18 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4) (M.op x 5)
def encoded (M : Magma (Fin 6)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)
theorem encoded_eq (M : Magma (Fin 6)) (x y : Fin 6) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1 else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3 else if bv x = 4 then rows M 4 else rows M 5) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3, M.op x 4, M.op x 5] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]
end N6

namespace N7
def bv (x : Fin 7) : BitVec 3 := BitVec.ofFin (x.castLE (by decide : 7 ≤ 8))
def clip (x : BitVec 3) : BitVec 3 := if x < 7 then x else 0
@[simp] theorem clip_bv (x : Fin 7) : clip (bv x) = bv x := by fin_cases x <;> decide
def pack (a0 a1 a2 a3 a4 a5 a6 : Fin 7) : BitVec 21 := bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0
@[spectrum_native]
theorem row_correct (a0 a1 a2 a3 a4 a5 a6 y : Fin 7) :
    ((pack a0 a1 a2 a3 a4 a5 a6 >>> ((bv y).setWidth 21 * 3)).setWidth 3) =
      bv (![a0, a1, a2, a3, a4, a5, a6] y) := by
  fin_cases y
  · change (((bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (0 : BitVec 21)).setWidth 3) = bv a0
    bv_decide
  · change (((bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (3 : BitVec 21)).setWidth 3) = bv a1
    bv_decide
  · change (((bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (6 : BitVec 21)).setWidth 3) = bv a2
    bv_decide
  · change (((bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (9 : BitVec 21)).setWidth 3) = bv a3
    bv_decide
  · change (((bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (12 : BitVec 21)).setWidth 3) = bv a4
    bv_decide
  · change (((bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (15 : BitVec 21)).setWidth 3) = bv a5
    bv_decide
  · change (((bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (18 : BitVec 21)).setWidth 3) = bv a6
    bv_decide
def op (a0 a1 a2 a3 a4 a5 a6 : BitVec 21) (x y : BitVec 3) : BitVec 3 :=
  clip (((if x = 0 then a0 else if x = 1 then a1 else if x = 2 then a2 else if x = 3 then a3 else if x = 4 then a4 else if x = 5 then a5 else a6) >>> (y.setWidth 21 * 3)).setWidth 3)
def rows (M : Magma (Fin 7)) (x : Fin 7) : BitVec 21 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4) (M.op x 5) (M.op x 6)
def encoded (M : Magma (Fin 7)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6)
theorem encoded_eq (M : Magma (Fin 7)) (x y : Fin 7) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1 else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3 else if bv x = 4 then rows M 4 else if bv x = 5 then rows M 5 else rows M 6) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3, M.op x 4, M.op x 5, M.op x 6] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]
end N7

end Spectrum.FiniteTableEncoding
