import equational_theories.Spectrum.Equation883Nine.Normalization

set_option maxHeartbeats 8000000
namespace Spectrum.E883Nine

def bv (x : Fin 9) : BitVec 4 := BitVec.ofFin (x.castLE (by decide : 9 ≤ 16))
def clip (x : BitVec 4) : BitVec 4 := if x < 9 then x else 0
@[simp] theorem clip_bv (x : Fin 9) : clip (bv x) = bv x := by fin_cases x <;> decide
def pack (a b c d e f g h i : Fin 9) : BitVec 36 := bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a

@[spectrum_native]
theorem row_correct (a b c d e f g h i y : Fin 9) :
    ((pack a b c d e f g h i >>> ((bv y).setWidth 36 * 4)).setWidth 4) =
      bv (![a,b,c,d,e,f,g,h,i] y) := by
  fin_cases y
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (0 : BitVec 36)).setWidth 4) = bv a
    bv_decide
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (4 : BitVec 36)).setWidth 4) = bv b
    bv_decide
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (8 : BitVec 36)).setWidth 4) = bv c
    bv_decide
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (12 : BitVec 36)).setWidth 4) = bv d
    bv_decide
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (16 : BitVec 36)).setWidth 4) = bv e
    bv_decide
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (20 : BitVec 36)).setWidth 4) = bv f
    bv_decide
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (24 : BitVec 36)).setWidth 4) = bv g
    bv_decide
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (28 : BitVec 36)).setWidth 4) = bv h
    bv_decide
  · change (((bv i ++ bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (32 : BitVec 36)).setWidth 4) = bv i
    bv_decide

def op (a b c d e f g h i : BitVec 36) (x y : BitVec 4) : BitVec 4 :=
  clip (((if x = 0 then a else if x = 1 then b else if x = 2 then c else if x = 3 then d else if x = 4 then e else if x = 5 then f else if x = 6 then g else if x = 7 then h else i) >>>
    (y.setWidth 36 * 4)).setWidth 4)

def rows (M : Magma (Fin 9)) (x : Fin 9) : BitVec 36 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4) (M.op x 5) (M.op x 6) (M.op x 7) (M.op x 8)
def encoded (M : Magma (Fin 9)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7) (rows M 8)

theorem encoded_eq (M : Magma (Fin 9)) (x y : Fin 9) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1 else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3 else if bv x = 4 then rows M 4 else if bv x = 5 then rows M 5 else if bv x = 6 then rows M 6 else if bv x = 7 then rows M 7 else rows M 8) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0,M.op x 1,M.op x 2,M.op x 3,M.op x 4,M.op x 5,M.op x 6,M.op x 7,M.op x 8] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]

end Spectrum.E883Nine
