import equational_theories.Definability.MatrixFamilyCounting
import Mathlib.Tactic.FinCases

/-! Matrices over `ZMod 9` that are diagonal modulo 3 form a finite clone family.
The four coordinates enumerate this subring without filtering the full matrix ring. -/

open Matrix Law Law.MagmaLaw Magma.MatrixFamily

namespace Magma.CongruenceMatrix

abbrev Q := ZMod 9 × ZMod 9 × ZMod 3 × ZMod 3
abbrev Params := Q × Q

private def lift (a : ZMod 3) : ZMod 9 := 3 * (a.val : ZMod 9)

private theorem lift_add : ∀ a b, lift (a + b) = lift a + lift b := by native_decide
private theorem lift_mul_left : ∀ (a : ZMod 9) b,
    lift ((a.cast : ZMod 3) * b) = a * lift b := by native_decide
private theorem lift_mul_right : ∀ a (b : ZMod 9),
    lift (a * (b.cast : ZMod 3)) = lift a * b := by native_decide
private theorem lift_mul_lift : ∀ a b, lift a * lift b = 0 := by native_decide

def embed (a : Q) : M (ZMod 9) 2 :=
  ![![a.1, lift a.2.2.1], ![lift a.2.2.2, a.2.1]]

def decode (a : M (ZMod 9) 2) : Q :=
  (a 0 0, a 1 1, ((a 0 1).val / 3 : ℕ), ((a 1 0).val / 3 : ℕ))

private theorem decode_embed : ∀ a, decode (embed a) = a := by native_decide

theorem embed_injective : Function.Injective embed :=
  Function.LeftInverse.injective decode_embed

def add (a b : Q) : Q :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2 + b.2.2.2)

def mul (a b : Q) : Q :=
  (a.1 * b.1, a.2.1 * b.2.1,
   (a.1.val : ZMod 3) * b.2.2.1 + a.2.2.1 * (b.2.1.val : ZMod 3),
   a.2.2.2 * (b.1.val : ZMod 3) + (a.2.1.val : ZMod 3) * b.2.2.2)

theorem embed_add (a b) : embed (add a b) = embed a + embed b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embed, add, lift_add]

theorem embed_mul (a b) : embed (mul a b) = embed a * embed b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embed, mul, Matrix.mul_apply, Fin.sum_univ_two,
      lift_add, lift_mul_left, lift_mul_right, lift_mul_lift]

def one : Q := (1, 1, 0, 0)
def zero : Q := (0, 0, 0, 0)
theorem embed_one : embed one = 1 := by decide
theorem embed_zero : embed zero = 0 := by decide

def pair (p : Params) : LP (ZMod 9) 2 := (embed p.1, embed p.2)
def operation (p : Params) := MatrixFamily.lin (pair p)
def composition (p q r : Params) : Params :=
  (add (mul p.1 q.1) (mul p.2 r.1), add (mul p.1 q.2) (mul p.2 r.2))

theorem operation_injective : Function.Injective operation := by
  intro p q h
  have he := lin_injective h
  exact Prod.ext (embed_injective (congrArg Prod.fst he))
    (embed_injective (congrArg Prod.snd he))

theorem operation_fst (x y : V (ZMod 9) 2) : operation (one, zero) x y = x := by
  simpa [operation, pair, embed_one, embed_zero] using lin_fst x y

theorem operation_snd (x y : V (ZMod 9) 2) : operation (zero, one) x y = y := by
  simpa [operation, pair, embed_one, embed_zero] using lin_snd x y

theorem operation_comp (p q r : Params) (x y : V (ZMod 9) 2) :
    operation (composition p q r) x y = operation p (operation q x y) (operation r x y) := by
  simpa [operation, pair, composition, linComp, embed_add, embed_mul] using
    lin_comp (pair p) (pair q) (pair r) x y

def Test {k : ℕ} (L : MagmaLaw (Fin k)) (p : Params) : Prop :=
  MatrixFamily.Test L (embed p.1, embed p.2, (0 : V (ZMod 9) 2))

instance {k : ℕ} (L : MagmaLaw (Fin k)) (p : Params) : Decidable (Test L p) := by
  unfold Test
  infer_instance

theorem test_iff_satisfies {k : ℕ} (L : MagmaLaw (Fin k)) (p : Params) :
    Test L p ↔ @satisfies _ (V (ZMod 9) 2) ⟨operation p⟩ L :=
  MatrixFamily.test_iff_satisfies L _

end Magma.CongruenceMatrix

/-- info: 'Magma.CongruenceMatrix.operation_comp' depends on axioms: [propext, Classical.choice, Quot.sound, Magma.CongruenceMatrix.lift_add._native.native_decide.ax_1_1, Magma.CongruenceMatrix.lift_mul_left._native.native_decide.ax_1_1, Magma.CongruenceMatrix.lift_mul_lift._native.native_decide.ax_1_1, Magma.CongruenceMatrix.lift_mul_right._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.CongruenceMatrix.operation_comp
/-- info: 'Magma.CongruenceMatrix.operation_injective' depends on axioms: [propext, Classical.choice, Quot.sound, Magma.CongruenceMatrix.decode_embed._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.CongruenceMatrix.operation_injective
/-- info: 'Magma.CongruenceMatrix.test_iff_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Magma.CongruenceMatrix.test_iff_satisfies
