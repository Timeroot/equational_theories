import equational_theories.Definability.CongruenceMatrixFamily

/-! Evaluate linear coefficients in the four-coordinate subring representation,
instead of repeatedly multiplying matrices during finite enumeration. -/
open Law FreeMagma

namespace Magma.CongruenceMatrix

def qcoeff {k : ℕ} (p : Params) : FreeMagma (Fin k) → Fin k → Q
  | .Leaf j => fun i => if i = j then one else zero
  | .Fork a b => fun i => add (mul p.1 (qcoeff p a i)) (mul p.2 (qcoeff p b i))

theorem coefficients_eq_qcoeff {k : ℕ} (p : Params) (t : FreeMagma (Fin k)) :
    MatrixFamily.coefficients (embed p.1, embed p.2, (0 : MatrixFamily.V (ZMod 9) 2)) t =
      (fun i => embed (qcoeff p t i), 0) := by
  induction t with
  | Leaf j =>
    apply Prod.ext
    · funext i
      by_cases h : i = j <;> simp [MatrixFamily.coefficients, qcoeff, h, embed_one, embed_zero]
    · rfl
  | Fork a b ha hb =>
    simp only [MatrixFamily.coefficients, ha, hb]
    apply Prod.ext
    · funext i
      simp [qcoeff, embed_add, embed_mul]
    · simp

def QTest {k : ℕ} (L : MagmaLaw (Fin k)) (p : Params) : Prop :=
  qcoeff p L.lhs = qcoeff p L.rhs

instance {k : ℕ} (L : MagmaLaw (Fin k)) (p : Params) : Decidable (QTest L p) := by
  unfold QTest
  infer_instance

theorem test_iff_qtest {k : ℕ} (L : MagmaLaw (Fin k)) (p : Params) :
    Test L p ↔ QTest L p := by
  unfold Test MatrixFamily.Test QTest
  rw [coefficients_eq_qcoeff, coefficients_eq_qcoeff]
  simp only [Prod.mk.injEq, and_true]
  constructor
  · intro h
    funext i
    exact embed_injective (congrFun h i)
  · intro h
    simp [h]

instance (priority := high) fastDecidableTest {k : ℕ} (L : MagmaLaw (Fin k)) (p : Params) :
    Decidable (Test L p) := decidable_of_iff (QTest L p) (test_iff_qtest L p).symm

end Magma.CongruenceMatrix

/-- info: 'Magma.CongruenceMatrix.test_iff_qtest' depends on axioms: [propext, Classical.choice, Quot.sound, Magma.CongruenceMatrix.decode_embed._native.native_decide.ax_1_1✝, Magma.CongruenceMatrix.lift_add._native.native_decide.ax_1_1✝, Magma.CongruenceMatrix.lift_mul_left._native.native_decide.ax_1_1✝, Magma.CongruenceMatrix.lift_mul_lift._native.native_decide.ax_1_1✝, Magma.CongruenceMatrix.lift_mul_right._native.native_decide.ax_1_1✝] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.CongruenceMatrix.test_iff_qtest
