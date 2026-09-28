import equational_theories.Spectrum.Basic
import equational_theories.Spectrum.Status
import Lean.Elab.Tactic.BVDecide
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace Spectrum.FiniteTableEncoding
namespace N8
def bv (x : Fin 8) : BitVec 3 := BitVec.ofFin (x.castLE (by decide : 8 ≤ 8))
def clip (x : BitVec 3) : BitVec 3 := x
@[simp] theorem clip_bv (x : Fin 8) : clip (bv x) = bv x := by fin_cases x <;> decide
def pack (a0 a1 a2 a3 a4 a5 a6 a7 : Fin 8) : BitVec 24 := bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0
@[spectrum_native]
theorem row_correct (a0 a1 a2 a3 a4 a5 a6 a7 y : Fin 8) :
    ((pack a0 a1 a2 a3 a4 a5 a6 a7 >>> ((bv y).setWidth 24 * 3)).setWidth 3) =
      bv (![a0, a1, a2, a3, a4, a5, a6, a7] y) := by
  fin_cases y
  · change (((bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (0 : BitVec 24)).setWidth 3) = bv a0
    bv_decide
  · change (((bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (3 : BitVec 24)).setWidth 3) = bv a1
    bv_decide
  · change (((bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (6 : BitVec 24)).setWidth 3) = bv a2
    bv_decide
  · change (((bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (9 : BitVec 24)).setWidth 3) = bv a3
    bv_decide
  · change (((bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (12 : BitVec 24)).setWidth 3) = bv a4
    bv_decide
  · change (((bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (15 : BitVec 24)).setWidth 3) = bv a5
    bv_decide
  · change (((bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (18 : BitVec 24)).setWidth 3) = bv a6
    bv_decide
  · change (((bv a7 ++ bv a6 ++ bv a5 ++ bv a4 ++ bv a3 ++ bv a2 ++ bv a1 ++ bv a0) >>> (21 : BitVec 24)).setWidth 3) = bv a7
    bv_decide
def op (a0 a1 a2 a3 a4 a5 a6 a7 : BitVec 24) (x y : BitVec 3) : BitVec 3 :=
  clip (((if x = 0 then a0 else if x = 1 then a1 else if x = 2 then a2 else if x = 3 then a3 else if x = 4 then a4 else if x = 5 then a5 else if x = 6 then a6 else a7) >>> (y.setWidth 24 * 3)).setWidth 3)
def rows (M : Magma (Fin 8)) (x : Fin 8) : BitVec 24 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4) (M.op x 5) (M.op x 6) (M.op x 7)
def encoded (M : Magma (Fin 8)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7)
theorem encoded_eq (M : Magma (Fin 8)) (x y : Fin 8) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1 else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3 else if bv x = 4 then rows M 4 else if bv x = 5 then rows M 5 else if bv x = 6 then rows M 6 else rows M 7) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3, M.op x 4, M.op x 5, M.op x 6, M.op x 7] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]
end N8

end Spectrum.FiniteTableEncoding
