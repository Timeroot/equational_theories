import equational_theories.Spectrum.Equation907

set_option maxHeartbeats 16000000
set_option maxRecDepth 32768

namespace Spectrum.E907Eight

def bv (x : Fin 8) : BitVec 3 := BitVec.ofFin x
def pack (a b c d e f g h : Fin 8) : BitVec 24 := bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a

@[spectrum_native]
theorem row_correct (a b c d e f g h y : Fin 8) :
    ((pack a b c d e f g h >>> ((bv y).setWidth 24 * 3)).setWidth 3) = bv (![a,b,c,d,e,f,g,h] y) := by
  fin_cases y
  · change (((bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (0 : BitVec 24)).setWidth 3) = bv a
    bv_decide
  · change (((bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (3 : BitVec 24)).setWidth 3) = bv b
    bv_decide
  · change (((bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (6 : BitVec 24)).setWidth 3) = bv c
    bv_decide
  · change (((bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (9 : BitVec 24)).setWidth 3) = bv d
    bv_decide
  · change (((bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (12 : BitVec 24)).setWidth 3) = bv e
    bv_decide
  · change (((bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (15 : BitVec 24)).setWidth 3) = bv f
    bv_decide
  · change (((bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (18 : BitVec 24)).setWidth 3) = bv g
    bv_decide
  · change (((bv h ++ bv g ++ bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (21 : BitVec 24)).setWidth 3) = bv h
    bv_decide

def op (a b c d e f g h : BitVec 24) (x y : BitVec 3) : BitVec 3 :=
  (((if x = 0 then a else if x = 1 then b else if x = 2 then c else if x = 3 then d else if x = 4 then e else if x = 5 then f else if x = 6 then g else h) >>> (y.setWidth 24 * 3)).setWidth 3)

def rows (M : Magma (Fin 8)) (x : Fin 8) : BitVec 24 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4) (M.op x 5) (M.op x 6) (M.op x 7)
def encoded (M : Magma (Fin 8)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5) (rows M 6) (rows M 7)

theorem encoded_eq (M : Magma (Fin 8)) (x y : Fin 8) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1 else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3 else if bv x = 4 then rows M 4 else if bv x = 5 then rows M 5 else if bv x = 6 then rows M 6 else rows M 7) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0,M.op x 1,M.op x 2,M.op x 3,M.op x 4,M.op x 5,M.op x 6,M.op x 7] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy]

end Spectrum.E907Eight
