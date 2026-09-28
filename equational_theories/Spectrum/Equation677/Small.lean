import equational_theories.Spectrum.FiniteTableEncoding
import equational_theories.Equations.All

/-! Exhaustive E677 exclusions at orders three and four, with checked finite-table encodings. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Spectrum.E677.Small3
def bv (x : Fin 3) : BitVec 2 := BitVec.ofFin (x.castLE (by decide : 3 ≤ 4))
def clip (x : BitVec 2) : BitVec 2 := if x < 3 then x else 0
@[simp] theorem clip_bv (x : Fin 3) : clip (bv x) = bv x := by fin_cases x <;> decide +kernel
def pack (a b c : Fin 3) : BitVec 6 := bv c ++ bv b ++ bv a
theorem row_correct : ∀ a b c y : Fin 3,
    ((pack a b c >>> ((bv y).setWidth 6 * 2)).setWidth 2) =
      bv (![a, b, c] y) := by decide +kernel
def op (a b c : BitVec 6) (x y : BitVec 2) : BitVec 2 :=
  clip (((if x = 0 then a else if x = 1 then b else c) >>> (y.setWidth 6 * 2)).setWidth 2)
def rows (M : Magma (Fin 3)) (x : Fin 3) : BitVec 6 :=
  pack (M.op x 0) (M.op x 1) (M.op x 2)
def encoded (M : Magma (Fin 3)) := op (rows M 0) (rows M 1) (rows M 2)
theorem encoded_eq (M : Magma (Fin 3)) (x y : Fin 3) :
    encoded M (bv x) (bv y) = bv (M.op x y) := by
  unfold encoded op
  have hx : (if bv x = 0 then rows M 0 else if bv x = 1 then rows M 1 else rows M 2) = rows M x := by
    fin_cases x <;> rfl
  rw [hx, rows, row_correct]
  have hy : ![M.op x 0, M.op x 1, M.op x 2] y = M.op x y := by
    fin_cases y <;> rfl
  rw [hy, clip_bv]

def test (a0 a1 a2 : BitVec 6) : Prop :=
  (0 : BitVec 2) = (op a0 a1 a2 0 (op a0 a1 a2 0 (op a0 a1 a2 (op a0 a1 a2 0 0) 0))) ∧
  (0 : BitVec 2) = (op a0 a1 a2 1 (op a0 a1 a2 0 (op a0 a1 a2 (op a0 a1 a2 1 0) 1))) ∧
  (0 : BitVec 2) = (op a0 a1 a2 2 (op a0 a1 a2 0 (op a0 a1 a2 (op a0 a1 a2 2 0) 2))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 0 (op a0 a1 a2 1 (op a0 a1 a2 (op a0 a1 a2 0 1) 0))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 1 (op a0 a1 a2 1 (op a0 a1 a2 (op a0 a1 a2 1 1) 1))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 2 (op a0 a1 a2 1 (op a0 a1 a2 (op a0 a1 a2 2 1) 2))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 0 (op a0 a1 a2 2 (op a0 a1 a2 (op a0 a1 a2 0 2) 0))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 1 (op a0 a1 a2 2 (op a0 a1 a2 (op a0 a1 a2 1 2) 1))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 2 (op a0 a1 a2 2 (op a0 a1 a2 (op a0 a1 a2 2 2) 2)))

@[spectrum_native]
theorem refute (a0 a1 a2 : BitVec 6) : ¬ test a0 a1 a2 := by
  unfold test op clip
  bv_check (config := { embeddedConstraintSubst := false }) "Three.lrat"
spectrum_assert refute complete

theorem impossible (M : Magma (Fin 3)) (h : @Equation677 (Fin 3) M) : False := by
  have H (x y : Fin 3) : bv x = encoded M (bv y)
      (encoded M (bv x) (encoded M (encoded M (bv y) (bv x)) (bv y))) := by
    simp only [encoded_eq]
    exact congrArg bv (h x y)
  apply refute (rows M 0) (rows M 1) (rows M 2)
  exact ⟨H 0 0, H 0 1, H 0 2, H 1 0, H 1 1, H 1 2, H 2 0, H 2 1, H 2 2⟩

end Spectrum.E677.Small3

theorem Spectrum.not_order_677_3 : ¬ Law677.HasModel 3 := by
  rintro ⟨M, hM⟩
  exact Spectrum.E677.Small3.impossible M ((@Law677.models_iff _ M).mp hM)
spectrum_assert Spectrum.not_order_677_3 complete
/-- info: 'Spectrum.not_order_677_3' depends on axioms: [propext, Classical.choice, Quot.sound, Spectrum.E677.Small3.refute._native.bv_decide.ax_1_5] -/
#guard_msgs (whitespace := lax) in
#print axioms Spectrum.not_order_677_3

namespace Spectrum.E677.Small4
open FiniteTableEncoding.N4

def test (a0 a1 a2 a3 : BitVec 8) : Prop :=
  (0 : BitVec 2) = (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 (op a0 a1 a2 a3 0 0) 0))) ∧
  (0 : BitVec 2) = (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 (op a0 a1 a2 a3 1 0) 1))) ∧
  (0 : BitVec 2) = (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 (op a0 a1 a2 a3 2 0) 2))) ∧
  (0 : BitVec 2) = (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 (op a0 a1 a2 a3 3 0) 3))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 (op a0 a1 a2 a3 0 1) 0))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 (op a0 a1 a2 a3 1 1) 1))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 (op a0 a1 a2 a3 2 1) 2))) ∧
  (1 : BitVec 2) = (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 (op a0 a1 a2 a3 3 1) 3))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 (op a0 a1 a2 a3 0 2) 0))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 (op a0 a1 a2 a3 1 2) 1))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 (op a0 a1 a2 a3 2 2) 2))) ∧
  (2 : BitVec 2) = (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 (op a0 a1 a2 a3 3 2) 3))) ∧
  (3 : BitVec 2) = (op a0 a1 a2 a3 0 (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 (op a0 a1 a2 a3 0 3) 0))) ∧
  (3 : BitVec 2) = (op a0 a1 a2 a3 1 (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 (op a0 a1 a2 a3 1 3) 1))) ∧
  (3 : BitVec 2) = (op a0 a1 a2 a3 2 (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 (op a0 a1 a2 a3 2 3) 2))) ∧
  (3 : BitVec 2) = (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 3 (op a0 a1 a2 a3 (op a0 a1 a2 a3 3 3) 3)))

@[spectrum_native]
theorem refute (a0 a1 a2 a3 : BitVec 8) : ¬ test a0 a1 a2 a3 := by
  unfold test op clip
  bv_check (config := { embeddedConstraintSubst := false }) "Four.lrat"
spectrum_assert refute complete

theorem impossible (M : Magma (Fin 4)) (h : @Equation677 (Fin 4) M) : False := by
  have H (x y : Fin 4) : bv x = encoded M (bv y)
      (encoded M (bv x) (encoded M (encoded M (bv y) (bv x)) (bv y))) := by
    simp only [encoded_eq]
    exact congrArg bv (h x y)
  apply refute (rows M 0) (rows M 1) (rows M 2) (rows M 3)
  exact ⟨H 0 0, H 0 1, H 0 2, H 0 3, H 1 0, H 1 1, H 1 2, H 1 3, H 2 0, H 2 1, H 2 2, H 2 3, H 3 0, H 3 1, H 3 2, H 3 3⟩

end Spectrum.E677.Small4

theorem Spectrum.not_order_677_4 : ¬ Law677.HasModel 4 := by
  rintro ⟨M, hM⟩
  exact Spectrum.E677.Small4.impossible M ((@Law677.models_iff _ M).mp hM)
spectrum_assert Spectrum.not_order_677_4 complete
/-- info: 'Spectrum.not_order_677_4' depends on axioms: [propext, Classical.choice, Quot.sound, Spectrum.E677.Small4.refute._native.bv_decide.ax_1_5] -/
#guard_msgs (whitespace := lax) in
#print axioms Spectrum.not_order_677_4
