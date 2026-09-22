import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

/-!
# Idempotent Latin squares

There is an idempotent Latin square of every positive order except two.
For odd order we use `2*x-y`. For even order we prolong the odd square
along the transversal `(x,x+1,x-1)`.
-/

namespace Spectrum

structure IdempotentLatin (Q : Type*) where
  op : Q → Q → Q
  idem : ∀ x, op x x = x
  row : ∀ x, Function.Bijective (op x)
  col : ∀ y, Function.Bijective (fun x => op x y)

namespace IdempotentLatin

variable {Q : Type*} (L : IdempotentLatin Q)

noncomputable def left (x z : Q) : Q := (Equiv.ofBijective (L.op x) (L.row x)).symm z
noncomputable def right (y z : Q) : Q :=
  (Equiv.ofBijective (fun x => L.op x y) (L.col y)).symm z

@[simp] theorem op_left (x z : Q) : L.op x (L.left x z) = z :=
  (Equiv.ofBijective (L.op x) (L.row x)).apply_symm_apply z
@[simp] theorem left_op (x y : Q) : L.left x (L.op x y) = y :=
  (Equiv.ofBijective (L.op x) (L.row x)).symm_apply_apply y
@[simp] theorem op_right (y z : Q) : L.op (L.right y z) y = z :=
  (Equiv.ofBijective (fun x => L.op x y) (L.col y)).apply_symm_apply z
@[simp] theorem right_op (x y : Q) : L.right y (L.op x y) = x :=
  (Equiv.ofBijective (fun x => L.op x y) (L.col y)).symm_apply_apply x

@[simp] theorem left_self (x : Q) : L.left x x = x := by
  simpa only [L.idem] using L.left_op x x
@[simp] theorem right_self (x : Q) : L.right x x = x := by
  simpa only [L.idem] using L.right_op x x
@[simp] theorem left_right (x y : Q) : L.left (L.right x y) y = x := by
  exact (congrArg (L.left (L.right x y)) (L.op_right x y)).symm.trans (L.left_op _ _)
@[simp] theorem right_left (x y : Q) : L.right (L.left x y) y = x := by
  exact (congrArg (L.right (L.left x y)) (L.op_left x y)).symm.trans (L.right_op _ _)

theorem op_ne_left {x y : Q} (h : x ≠ y) : L.op x y ≠ x := by
  intro e
  exact h ((L.row x).injective (e.trans (L.idem x).symm)).symm
theorem op_ne_right {x y : Q} (h : x ≠ y) : L.op x y ≠ y := by
  intro e
  exact h ((L.col y).injective (e.trans (L.idem y).symm))
theorem left_ne_left {x y : Q} (h : x ≠ y) : L.left x y ≠ x := by
  intro e
  have := L.op_left x y
  rw [e, L.idem] at this
  exact h this
theorem left_ne_right {x y : Q} (h : x ≠ y) : L.left x y ≠ y := by
  intro e
  have := L.op_left x y
  rw [e] at this
  exact L.op_ne_right h this
theorem right_ne_left {x y : Q} (h : x ≠ y) : L.right x y ≠ x := by
  intro e
  have := L.op_right x y
  rw [e, L.idem] at this
  exact h this
theorem right_ne_right {x y : Q} (h : x ≠ y) : L.right x y ≠ y := by
  intro e
  have := L.op_right x y
  rw [e] at this
  exact L.op_ne_left h.symm this

private theorem two_injective {n : ℕ} (h : Odd n) :
    Function.Injective (fun x : ZMod n => 2 * x) := by
  have hu : IsUnit (2 : ZMod n) := (ZMod.isUnit_iff_coprime 2 n).mpr h.coprime_two_left
  exact hu.mul_right_injective

/-- The odd-order idempotent Latin square. -/
def odd (n : ℕ) [NeZero n] (h : Odd n) : IdempotentLatin (ZMod n) where
  op x y := 2*x-y
  idem x := by ring
  row x := (Finite.injective_iff_bijective).mp (by intro y z e; linear_combination -e)
  col y := (Finite.injective_iff_bijective).mp (by
    intro x z e
    apply two_injective h
    linear_combination e)

/-- Prolong the transversal `(x,x+1,x-1)` by a new point. -/
def prolongOp {n : ℕ} : Option (ZMod n) → Option (ZMod n) → Option (ZMod n)
  | none, none => none
  | some x, none => some (x-1)
  | none, some y => some (y-2)
  | some x, some y => if y = x+1 then none else some (2*x-y)

private theorem zmod_one_ne_zero {n : ℕ} (hn : 3 ≤ n) : (1 : ZMod n) ≠ 0 := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  exact _root_.one_ne_zero

def prolong (n : ℕ) [NeZero n] (h : Odd n) (hn : 3 ≤ n) :
    IdempotentLatin (Option (ZMod n)) where
  op := prolongOp
  idem x := by
    cases x with
    | none => rfl
    | some x =>
      have hx : x ≠ x+1 := by
        intro e
        exact zmod_one_ne_zero hn (by linear_combination -e)
      simp only [prolongOp, if_neg hx, Option.some.injEq]
      ring
  row x := (Finite.injective_iff_bijective).mp (by
    intro y z e
    cases x <;> cases y <;> cases z <;> simp only [prolongOp] at e ⊢
    all_goals try split_ifs at e
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    all_goals try first | rfl | contradiction | (linear_combination e) | (linear_combination -e)
    all_goals apply_assumption
    all_goals first | (linear_combination e) | (linear_combination -e))
  col y := (Finite.injective_iff_bijective).mp (by
    intro x z e
    cases y <;> cases x <;> cases z <;> simp only [prolongOp] at e ⊢
    all_goals try split_ifs at e
    all_goals simp_all only [Option.some.injEq, reduceCtorEq]
    all_goals try simp_all only [add_left_inj]
    all_goals try first | rfl | contradiction | (linear_combination e) | (linear_combination -e) | (apply two_injective h; linear_combination e)
    all_goals apply_assumption
    all_goals apply two_injective h
    all_goals first | (linear_combination e) | (linear_combination -e))

/-- Every positive order other than two admits an idempotent Latin square. -/
theorem exists_card (n : ℕ) (hn : 0 < n) (hn2 : n ≠ 2) :
    ∃ (Q : Type) (f : Fintype Q), Nonempty (IdempotentLatin Q) ∧ @Fintype.card Q f = n := by
  haveI : NeZero n := ⟨by omega⟩
  by_cases h : Odd n
  · exact ⟨ZMod n, inferInstance, ⟨odd n h⟩, ZMod.card n⟩
  · have hodd : Odd (n-1) := by
      rw [Nat.odd_iff] at h ⊢
      omega
    have hm : 3 ≤ n-1 := by
      rw [Nat.odd_iff] at h
      omega
    haveI : NeZero (n-1) := ⟨by omega⟩
    refine ⟨Option (ZMod (n-1)), inferInstance, ⟨prolong (n-1) hodd hm⟩, ?_⟩
    simp only [Fintype.card_option, ZMod.card]
    omega

end IdempotentLatin
end Spectrum
