import equational_theories.Spectrum.Mendelsohn
import Lean.Elab.Tactic.BVDecide
import equational_theories.Spectrum.Status

/-!
# The exceptional order six

A bit-vector certificate rules out all idempotent semisymmetric operations on
six elements. The encoding is proved to represent every such operation, and
`bv_decide` verifies its LRAT certificate using Lean's native proof checker.
The two native computations are explicitly registered with the spectrum audit.
-/

set_option maxHeartbeats 4000000
namespace Spectrum.MendelsohnSix

def bv (x : Fin 6) : BitVec 3 := BitVec.ofFin (x.castLE (by decide : 6 ≤ 8))
def clip (x : BitVec 3) : BitVec 3 := if x < 6 then x else 0

@[simp] theorem clip_bv (x : Fin 6) : clip (bv x) = bv x := by fin_cases x <;> decide

def pack (a b c d e f : Fin 6) : BitVec 18 := bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a

@[spectrum_native]
theorem row_correct (a b c d e f y : Fin 6) :
    ((pack a b c d e f >>> ((bv y).setWidth 18 * 3)).setWidth 3) =
      bv (![a,b,c,d,e,f] y) := by
  fin_cases y
  · change (((bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (0 : BitVec 18)).setWidth 3) = bv a
    bv_decide
  · change (((bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (3 : BitVec 18)).setWidth 3) = bv b
    bv_decide
  · change (((bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (6 : BitVec 18)).setWidth 3) = bv c
    bv_decide
  · change (((bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (9 : BitVec 18)).setWidth 3) = bv d
    bv_decide
  · change (((bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (12 : BitVec 18)).setWidth 3) = bv e
    bv_decide
  · change (((bv f ++ bv e ++ bv d ++ bv c ++ bv b ++ bv a) >>> (15 : BitVec 18)).setWidth 3) = bv f
    bv_decide

def op (a b c d e f : BitVec 18) (x y : BitVec 3) : BitVec 3 :=
  if x = y then x else
    clip (((if x = 0 then a else if x = 1 then b else if x = 2 then c
      else if x = 3 then d else if x = 4 then e else f) >>>
      (y.setWidth 18 * 3)).setWidth 3)

def rows (M : Mendelsohn (Fin 6)) (x : Fin 6) : BitVec 18 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4) (M.op x 5)
def encoded (M : Mendelsohn (Fin 6)) := op (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)

theorem encoded_eq (M : Mendelsohn (Fin 6)) (x y : Fin 6) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  have hinj : Function.Injective bv := by decide
  by_cases h : x = y
  · subst y; simp [encoded, op, M.idem]
  have hb : bv x ≠ bv y := fun e => h (hinj e)
  simp only [encoded, op, if_neg hb]
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1
      else if bv x = 2 then rows M 2 else if bv x = 3 then rows M 3
      else if bv x = 4 then rows M 4 else rows M 5) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3, M.op x 4, M.op x 5] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]

def test (a b c d e f : BitVec 18) : Prop :=
  op a b c d e f 1 (op a b c d e f 0 1) = 0 ∧
  op a b c d e f 2 (op a b c d e f 0 2) = 0 ∧
  op a b c d e f 3 (op a b c d e f 0 3) = 0 ∧
  op a b c d e f 4 (op a b c d e f 0 4) = 0 ∧
  op a b c d e f 5 (op a b c d e f 0 5) = 0 ∧
  op a b c d e f 0 (op a b c d e f 1 0) = 1 ∧
  op a b c d e f 2 (op a b c d e f 1 2) = 1 ∧
  op a b c d e f 3 (op a b c d e f 1 3) = 1 ∧
  op a b c d e f 4 (op a b c d e f 1 4) = 1 ∧
  op a b c d e f 5 (op a b c d e f 1 5) = 1 ∧
  op a b c d e f 0 (op a b c d e f 2 0) = 2 ∧
  op a b c d e f 1 (op a b c d e f 2 1) = 2 ∧
  op a b c d e f 3 (op a b c d e f 2 3) = 2 ∧
  op a b c d e f 4 (op a b c d e f 2 4) = 2 ∧
  op a b c d e f 5 (op a b c d e f 2 5) = 2 ∧
  op a b c d e f 0 (op a b c d e f 3 0) = 3 ∧
  op a b c d e f 1 (op a b c d e f 3 1) = 3 ∧
  op a b c d e f 2 (op a b c d e f 3 2) = 3 ∧
  op a b c d e f 4 (op a b c d e f 3 4) = 3 ∧
  op a b c d e f 5 (op a b c d e f 3 5) = 3 ∧
  op a b c d e f 0 (op a b c d e f 4 0) = 4 ∧
  op a b c d e f 1 (op a b c d e f 4 1) = 4 ∧
  op a b c d e f 2 (op a b c d e f 4 2) = 4 ∧
  op a b c d e f 3 (op a b c d e f 4 3) = 4 ∧
  op a b c d e f 5 (op a b c d e f 4 5) = 4 ∧
  op a b c d e f 0 (op a b c d e f 5 0) = 5 ∧
  op a b c d e f 1 (op a b c d e f 5 1) = 5 ∧
  op a b c d e f 2 (op a b c d e f 5 2) = 5 ∧
  op a b c d e f 3 (op a b c d e f 5 3) = 5 ∧
  op a b c d e f 4 (op a b c d e f 5 4) = 5

@[spectrum_native]
theorem refute (a b c d e f : BitVec 18) : ¬ test a b c d e f := by
  unfold test op clip
  bv_decide (config := { timeout := 60 })

theorem impossible (M : Mendelsohn (Fin 6)) : False := by
  apply refute (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)
  have h (x y : Fin 6) : encoded M (bv y) (encoded M (bv x) (bv y)) = bv x := by
    rw [encoded_eq, encoded_eq, M.semi]
  change test (rows M 0) (rows M 1) (rows M 2) (rows M 3) (rows M 4) (rows M 5)
  unfold test
  exact ⟨h 0 1, h 0 2, h 0 3, h 0 4, h 0 5, h 1 0, h 1 2, h 1 3, h 1 4, h 1 5, h 2 0, h 2 1, h 2 3, h 2 4, h 2 5, h 3 0, h 3 1, h 3 2, h 3 4, h 3 5, h 4 0, h 4 1, h 4 2, h 4 3, h 4 5, h 5 0, h 5 1, h 5 2, h 5 3, h 5 4⟩

end Spectrum.MendelsohnSix
