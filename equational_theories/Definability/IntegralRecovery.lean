import equational_theories.Definability.Linear
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Algebraic-integer obstructions to term recovery

On `ℂ`, the operation `(-(1+i)/2)*x + i*y` satisfies E467. Its first
coefficient is not an algebraic integer. In contrast, every complex-linear
model of E667, E917, E1086, or E1729 has algebraic-integer coefficients.
Such operations and all their terms preserve the algebraic integers, whereas
the source does not. These are arbitrary-carrier term-structural negatives only.
-/

open Law Law.MagmaLaw Magma Polynomial

namespace IntegralRecovery

variable {R : Type} [CommRing R]

/-- The shared coefficient equations for E917 force integrality. -/
theorem integral_coefficients (a b : R) (h1 : a * b ^ 2 = 1)
    (h2 : a + a ^ 2 * b + a * b ^ 2 + b ^ 3 = 0) :
    IsIntegral ℤ a ∧ IsIntegral ℤ b := by
  have hp : b ^ 6 + b ^ 3 + b + 1 = 0 := by
    linear_combination b ^ 3 * h2 - (a * b ^ 2 + 1 + b ^ 3 + b) * h1
  have hb : IsIntegral ℤ b := by
    refine ⟨X ^ 6 + X ^ 3 + X + 1, by monicity!, ?_⟩
    simpa using hp
  let q := b ^ 5 + b ^ 2 + 1
  have hq : b * q = -1 := by dsimp [q]; linear_combination hp
  have ha : a = q ^ 2 := by
    linear_combination q ^ 2 * h1 - a * (b * q - 1) * hq
  rw [ha]
  exact ⟨((hb.pow 5).add (hb.pow 2) |>.add isIntegral_one).pow 2, hb⟩

theorem integral_667 (a b : R) (h : @Equation667 R (lin a b)) :
    IsIntegral ℤ a ∧ IsIntegral ℤ b := by
  have h1 := h 1 0
  have h2 := h 0 1
  simp only [lin_op] at h1 h2
  have ha : a = -b ^ 3 := by linear_combination -h2
  have hp : b ^ 8 - b ^ 6 - b ^ 4 - 1 = 0 := by
    rw [ha] at h1
    linear_combination -h1
  have hb : IsIntegral ℤ b := by
    refine ⟨X ^ 8 - X ^ 6 - X ^ 4 - 1, by monicity!, ?_⟩
    simpa using hp
  exact ⟨by rw [ha]; exact (hb.pow 3).neg, hb⟩

theorem integral_917 (a b : R) (h : @Equation917 R (lin a b)) :
    IsIntegral ℤ a ∧ IsIntegral ℤ b := by
  have h1 := h 1 0
  have h2 := h 0 1
  simp only [lin_op] at h1 h2
  exact integral_coefficients a b (by linear_combination -h1) (by linear_combination -h2)

theorem integral_1729 (a b : R) (h : @Equation1729 R (lin a b)) :
    IsIntegral ℤ a ∧ IsIntegral ℤ b := by
  have h1 := h 1 0
  have h2 := h 0 1
  simp only [lin_op] at h1 h2
  exact integral_coefficients a b (by linear_combination -h1)
    (by linear_combination -b * h2 + a * h1)

theorem integral_1086 (a b : R) (h : @Equation1086 R (lin a b)) :
    IsIntegral ℤ a ∧ IsIntegral ℤ b := by
  have h1 := h 1 0
  have h2 := h 0 1
  simp only [lin_op] at h1 h2
  have hc : IsIntegral ℤ b ∧ IsIntegral ℤ a :=
    integral_coefficients b a (by linear_combination -h1)
      (by linear_combination -a ^ 2 * h2 + (a ^ 2 * b + a * b ^ 2 + b) * h1)
  exact hc.symm

noncomputable section

def sourceA : ℂ := -(1 + Complex.I) / 2

theorem source_law : @Equation467 ℂ (lin sourceA Complex.I) := by
  intro x y
  simp only [lin_op, sourceA]
  linear_combination (-Complex.I ^ 2 * y / 2 + Complex.I * (x / 2 + y / 2) +
    x + y / 2) * Complex.I_sq

theorem half_not_integral : ¬ IsIntegral ℤ (1 / 2 : ℂ) := by
  intro h
  have hq : IsIntegral ℤ (1 / 2 : ℚ) := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (B := ℂ)
      (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp
    simpa using h
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  change (z : ℚ) = 1 / 2 at hz
  have : (2 : ℚ) * z = 1 := by rw [hz]; norm_num
  have hz' : 2 * z = 1 := by exact_mod_cast this
  omega

theorem sourceA_not_integral : ¬ IsIntegral ℤ sourceA := by
  intro h
  apply half_not_integral
  have he : -(sourceA * (sourceA + 1)) = (1 / 2 : ℂ) := by
    dsimp [sourceA]
    linear_combination (-1 / 4 : ℂ) * Complex.I_sq
  rw [← he]
  exact (h.mul (h.add isIntegral_one)).neg

/-- Algebraic integers form a subring, hence are preserved by every term of
an operation with algebraic-integer coefficients. -/
def PreservesIntegral (f : ℂ → ℂ → ℂ) : Prop :=
  ∀ x y, IsIntegral ℤ x → IsIntegral ℤ y → IsIntegral ℤ (f x y)

theorem preservesIntegral_invariant {N : Magma ℂ} (h : PreservesIntegral N.op) :
    N.IsCloneInvariant PreservesIntegral where
  fst := fun _ _ hx _ => hx
  snd := fun _ _ _ hy => hy
  comp := fun _ _ hf hg x y hx hy => h _ _ (hf x y hx hy) (hg x y hx hy)

theorem not_termStructural (L : NatMagmaLaw)
    (hL : ∀ a b : ℂ, @satisfies _ ℂ (lin a b) L → IsIntegral ℤ a ∧ IsIntegral ℤ b) :
    ¬ L.TermStructuralFrom Law467 := by
  intro h
  obtain ⟨N, hN, hfwd, hback⟩ := h (lin sourceA Complex.I)
    ((@Law467.models_iff ℂ (lin sourceA Complex.I)).mpr source_law)
  obtain ⟨a, b, _, hop, _⟩ :=
    (lin_isCloneInvariant sourceA Complex.I (sourceA + Complex.I - 1) 1 (by ring)).of_termDefinable hfwd
  have hEq : N = lin a b := by
    cases N
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst N
  obtain ⟨ha, hb⟩ := hL a b hN
  have hn : PreservesIntegral (lin a b).op :=
    fun x y hx hy => (ha.mul hx).add (hb.mul hy)
  have hm := (preservesIntegral_invariant hn).of_termDefinable hback
  apply sourceA_not_integral
  simpa [lin_op] using hm 1 0 isIntegral_one isIntegral_zero

end

end IntegralRecovery

theorem Equation667_not_termStructuralFrom_Equation467_integral :
    ¬ Law667.TermStructuralFrom Law467 :=
  IntegralRecovery.not_termStructural Law667 fun a b h =>
    IntegralRecovery.integral_667 a b ((@Law667.models_iff ℂ (Magma.lin a b)).mp h)

/-- info: 'Equation667_not_termStructuralFrom_Equation467_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation667_not_termStructuralFrom_Equation467_integral

theorem Equation917_not_termStructuralFrom_Equation467_integral :
    ¬ Law917.TermStructuralFrom Law467 :=
  IntegralRecovery.not_termStructural Law917 fun a b h =>
    IntegralRecovery.integral_917 a b ((@Law917.models_iff ℂ (Magma.lin a b)).mp h)

/-- info: 'Equation917_not_termStructuralFrom_Equation467_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation917_not_termStructuralFrom_Equation467_integral

theorem Equation1086_not_termStructuralFrom_Equation467_integral :
    ¬ Law1086.TermStructuralFrom Law467 :=
  IntegralRecovery.not_termStructural Law1086 fun a b h =>
    IntegralRecovery.integral_1086 a b ((@Law1086.models_iff ℂ (Magma.lin a b)).mp h)

/-- info: 'Equation1086_not_termStructuralFrom_Equation467_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation1086_not_termStructuralFrom_Equation467_integral

theorem Equation1729_not_termStructuralFrom_Equation467_integral :
    ¬ Law1729.TermStructuralFrom Law467 :=
  IntegralRecovery.not_termStructural Law1729 fun a b h =>
    IntegralRecovery.integral_1729 a b ((@Law1729.models_iff ℂ (Magma.lin a b)).mp h)

/-- info: 'Equation1729_not_termStructuralFrom_Equation467_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation1729_not_termStructuralFrom_Equation467_integral
