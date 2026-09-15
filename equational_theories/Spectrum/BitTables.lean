import equational_theories.Spectrum.Finite
import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.BVDecide

/-!
# Bit-vector tables with a prescribed squaring map

Rows occupy 8 bits at order four and 15 bits at order five. The diagonal is
supplied separately, so normalizing a squaring map exposes constants before
bit-blasting. The encoding lemmas connect the SAT predicates to actual magmas;
neither SAT nor the generator is trusted to perform that conversion.
-/

open Law
namespace Spectrum.BitTables

def bv4 (x : Fin 4) : BitVec 2 := BitVec.ofFin x
def bv5 (x : Fin 5) : BitVec 3 := BitVec.ofFin (x.castLE (by decide : 5 ≤ 8))

theorem bv4_injective : Function.Injective bv4 := by decide
theorem bv5_injective : Function.Injective bv5 := by decide

def pack4 (a b c d : Fin 4) : BitVec 8 := bv4 d ++ bv4 c ++ bv4 b ++ bv4 a
def pack5 (a b c d e : Fin 5) : BitVec 15 := bv5 e ++ bv5 d ++ bv5 c ++ bv5 b ++ bv5 a

@[spectrum_native]
theorem row4_correct : ∀ a b c d y : Fin 4,
    ((pack4 a b c d >>> ((bv4 y).setWidth 8 * 2)).setWidth 2) =
      bv4 (![a, b, c, d] y) := by native_decide

@[spectrum_native]
theorem row5_correct : ∀ a b c d e y : Fin 5,
    ((pack5 a b c d e >>> ((bv5 y).setWidth 15 * 3)).setWidth 3) =
      bv5 (![a, b, c, d, e] y) := by native_decide

def rows4 (M : Magma (Fin 4)) (x : Fin 4) : BitVec 8 :=
  pack4 (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3)
def rows5 (M : Magma (Fin 5)) (x : Fin 5) : BitVec 15 :=
  pack5 (M.op x 0) (M.op x 1) (M.op x 2) (M.op x 3) (M.op x 4)

def op4 (s : BitVec 2 → BitVec 2) (a b c d : BitVec 8) (x y : BitVec 2) : BitVec 2 :=
  if x = y then s x else
    ((if x = 0 then a else if x = 1 then b else if x = 2 then c else d) >>>
      (y.setWidth 8 * 2)).setWidth 2

def clip5 (x : BitVec 3) : BitVec 3 := if x < 4 then x else 4

def op5 (s : BitVec 3 → BitVec 3) (a b c d e : BitVec 15) (x y : BitVec 3) : BitVec 3 :=
  let x := clip5 x
  let y := clip5 y
  if x = y then s x else
    ((if x = 0 then a else if x = 1 then b else if x = 2 then c else if x = 3 then d else e) >>>
      (y.setWidth 15 * 3)).setWidth 3

theorem clip5_bv (x : Fin 5) : clip5 (bv5 x) = bv5 x := by fin_cases x <;> decide

def encoded4 (M : Magma (Fin 4)) (s : BitVec 2 → BitVec 2) :=
  op4 s (rows4 M 0) (rows4 M 1) (rows4 M 2) (rows4 M 3)
def encoded5 (M : Magma (Fin 5)) (s : BitVec 3 → BitVec 3) :=
  op5 s (rows5 M 0) (rows5 M 1) (rows5 M 2) (rows5 M 3) (rows5 M 4)

theorem encoded4_eq (M : Magma (Fin 4)) (s : BitVec 2 → BitVec 2)
    (hs : ∀ x, s (bv4 x) = bv4 (M.op x x)) (x y : Fin 4) :
    encoded4 M s (bv4 x) (bv4 y) = bv4 (M.op x y) := by
  by_cases h : x = y
  · subst y; simpa [encoded4, op4] using hs x
  have hb : bv4 x ≠ bv4 y := fun hxy => h (bv4_injective hxy)
  simp only [encoded4, op4, if_neg hb]
  have hx : (if bv4 x = 0 then rows4 M 0 else if bv4 x = 1 then rows4 M 1
      else if bv4 x = 2 then rows4 M 2 else rows4 M 3) = rows4 M x := by
    fin_cases x <;> rfl
  rw [hx]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3] y = M.op x y := by
    fin_cases y <;> rfl
  exact (row4_correct _ _ _ _ y).trans (congrArg bv4 hy)

theorem encoded5_eq (M : Magma (Fin 5)) (s : BitVec 3 → BitVec 3)
    (hs : ∀ x, s (bv5 x) = bv5 (M.op x x)) (x y : Fin 5) :
    encoded5 M s (bv5 x) (bv5 y) = bv5 (M.op x y) := by
  simp only [encoded5, op5, clip5_bv]
  by_cases h : x = y
  · subst y; simpa using hs x
  have hb : bv5 x ≠ bv5 y := fun hxy => h (bv5_injective hxy)
  simp only [if_neg hb]
  have hx : (if bv5 x = 0 then rows5 M 0 else if bv5 x = 1 then rows5 M 1
      else if bv5 x = 2 then rows5 M 2 else if bv5 x = 3 then rows5 M 3 else rows5 M 4) =
      rows5 M x := by fin_cases x <;> rfl
  rw [hx]
  have hy : ![M.op x 0, M.op x 1, M.op x 2, M.op x 3, M.op x 4] y = M.op x y := by
    fin_cases y <;> rfl
  exact (row5_correct _ _ _ _ _ y).trans (congrArg bv5 hy)

spectrum_assert encoded4_eq complete
spectrum_assert encoded5_eq complete
end Spectrum.BitTables
