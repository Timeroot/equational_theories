import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Field.Rat
import equational_theories.Definability.Linear

/-! A linear E680 magma over the rational dual numbers cannot be recovered
by terms from an E14 companion: every linear E14 operation has coefficients
`-1, -1`, and hence preserves the rational subring, while the source does not. -/

open Law Law.MagmaLaw
namespace DualNumberRecovery
open TrivSqZeroExt
open scoped DualNumber

abbrev R := DualNumber ℚ
@[reducible] def base : Magma R := Magma.lin (-1 + ε) (-1 - ε)

theorem source_law : @Equation680 R base := by
  intro x y
  apply TrivSqZeroExt.ext <;> simp [Magma.lin_op] <;> ring

theorem coefficients14 (a b : R) (h : @Equation14 R (Magma.lin a b)) :
    a = -1 ∧ b = -1 := by
  have h1 : a * b = 1 := by
    have := h 1 0
    simp only [Magma.lin_op] at this
    linear_combination -this
  have h2 : a + b ^ 2 = 0 := by
    have := h 0 1
    simp only [Magma.lin_op] at this
    linear_combination -this
  have h3 : b ^ 3 = -1 := by linear_combination b * h2 - h1
  have hfirst : b.fst ^ 3 = (-1 : ℚ) ^ 3 := by
    have := congrArg TrivSqZeroExt.fst h3
    simpa using this
  have hbfirst : b.fst = -1 := by
    exact (Odd.pow_inj (by decide : Odd 3)).mp hfirst
  have hbsecond : b.snd = 0 := by
    have := congrArg TrivSqZeroExt.snd h3
    simp [pow_succ, hbfirst] at this
    linear_combination (1 / 3 : ℚ) * this
  have hb : b = -1 := by
    apply TrivSqZeroExt.ext <;> simp [hbfirst, hbsecond]
  refine ⟨?_, hb⟩
  rw [hb] at h2
  linear_combination h2

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
    (Magma.lin_isCloneInvariant (-1 + (ε : R)) (-1 - ε) (-3) 1 (by ring)).of_termDefinable hfwd
  have hEq : N = Magma.lin a b := by
    cases N
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst N
  obtain ⟨rfl, rfl⟩ := coefficients14 a b ((@Law14.models_iff R (Magma.lin a b)).mp hN)
  have hp : PreservesConstants (Magma.lin (-1 : R) (-1)).op := by
    intro x y hx hy
    simp [Magma.lin_op, hx, hy]
  have hm := (preservesConstants_invariant _ hp).of_termDefinable hback
  have := hm 1 0 rfl rfl
  norm_num [base, Magma.lin_op] at this

end DualNumberRecovery
