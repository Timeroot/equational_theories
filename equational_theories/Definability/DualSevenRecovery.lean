import equational_theories.Definability.DualNumberRecovery
import Mathlib.Algebra.Field.ZMod

/-! Over the dual numbers over `ZMod 7`, the coefficients
`a = -(5 + ε)^2`, `b = 5 + ε` satisfy E115. Every linear E14 operation
preserves the constant subring, while this operation does not. -/

open Law Law.MagmaLaw
namespace DualSevenRecovery
open TrivSqZeroExt
open scoped DualNumber

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

abbrev R := DualNumber (ZMod 7)
@[simp] theorem fst_five : (5 : R).fst = (5 : ZMod 7) := rfl
@[simp] theorem snd_five : (5 : R).snd = 0 := rfl
@[reducible] def base : Magma R := Magma.lin (- (5 + ε) ^ 2) (5 + ε)

theorem source_law : @Equation115 R base := by
  intro x y
  apply TrivSqZeroExt.ext
  · simp [Magma.lin_op]
    ring_nf
    change x.fst = x.fst * (2500 : ZMod 7)
    rw [show (2500 : ZMod 7) = 1 by decide, mul_one]
  · simp [Magma.lin_op]
    ring_nf
    change x.snd = x.fst * (2625 : ZMod 7) + x.snd * (2500 : ZMod 7)
    rw [show (2500 : ZMod 7) = 1 by decide, show (2625 : ZMod 7) = 0 by decide]
    simp

theorem coefficients14 (a b : R) (h : @Equation14 R (Magma.lin a b)) :
    a.snd = 0 ∧ b.snd = 0 := by
  have h1 : a * b = 1 := by
    have := h 1 0
    simp only [Magma.lin_op] at this
    linear_combination -this
  have h2 : a + b ^ 2 = 0 := by
    have := h 0 1
    simp only [Magma.lin_op] at this
    linear_combination -this
  have h3 : b ^ 3 = -1 := by linear_combination b * h2 - h1
  have hbfirst : b.fst ≠ 0 := by
    intro he
    have := congrArg TrivSqZeroExt.fst h3
    simp [he] at this
  have hbsecond : b.snd = 0 := by
    have hh := congrArg TrivSqZeroExt.snd h3
    have hq : (3 : ZMod 7) * b.fst ^ 2 * b.snd = 0 := by
      simp [pow_succ] at hh
      linear_combination hh
    simpa only [mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0), hbfirst,
      show (3 : ZMod 7) ≠ 0 by decide, false_or] using hq
  refine ⟨?_, hbsecond⟩
  have hh := congrArg TrivSqZeroExt.snd h2
  simpa [pow_succ, hbsecond] using hh

def PreservesConstants (f : R → R → R) : Prop :=
  ∀ x y, x.snd = 0 → y.snd = 0 → (f x y).snd = 0

theorem preservesConstants_invariant (M : Magma R) (h : PreservesConstants M.op) :
    M.IsCloneInvariant PreservesConstants where
  fst := fun _ _ hx _ => hx
  snd := fun _ _ _ hy => hy
  comp := fun _ _ hf hg x y hx hy => h _ _ (hf x y hx hy) (hg x y hx hy)

theorem no_recovery : ¬ Law14.TermStructuralOnMagma base := by
  rintro ⟨N, hN, hfwd, hback⟩
  obtain ⟨a, b, _, hop, _⟩ :=
    (Magma.lin_isCloneInvariant (- (5 + (ε : R)) ^ 2) (5 + ε) 1
      (- (5 + ε) ^ 2 + (5 + ε) - 1) (by ring)).of_termDefinable hfwd
  have hEq : N = Magma.lin a b := by
    cases N
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst N
  obtain ⟨ha, hb⟩ := coefficients14 a b ((@Law14.models_iff R (Magma.lin a b)).mp hN)
  have hp : PreservesConstants (Magma.lin a b).op := by
    intro x y hx hy
    simp [Magma.lin_op, ha, hb, hx, hy]
  have hm := (preservesConstants_invariant _ hp).of_termDefinable hback
  have := hm 0 1 rfl rfl
  norm_num [base, Magma.lin_op] at this

end DualSevenRecovery
