import equational_theories.Definability.LinearGaussian
import Mathlib.Tactic.IntervalCases

/-!
# Gaussian-integer obstructions to term recovery

The source operation is `x ◇ y = i * (x - y)` on `ℤ[i]`, a model of E1496.
Any term-defined companion is Gaussian-linear. E680, E1113 and E1682 constrain its
coefficients to units. Such a companion either preserves the real integers, or has coefficient
sum 1 in one of the residue fields above 5. Both properties persist under terms;
the source operation has neither. This is an infinite-carrier obstruction to
term-structural definability, not to finite or first-order definability.
-/

open Law Law.MagmaLaw

namespace GaussianRecovery

open Magma
local notation "ℤ[i]" => GaussianInt

/-- One of three proper subclones will prevent recovery of the source. -/
def Trapped (a b : ℤ[i]) : Prop :=
  (a.im = 0 ∧ b.im = 0) ∨ gi5a (a + b) = 1 ∨ gi5b (a + b) = 1

instance (a b : ℤ[i]) : Decidable (Trapped a b) := by unfold Trapped; infer_instance

theorem unit_cases (a : ℤ[i]) (ha : IsUnit a) :
    a = 1 ∨ a = -1 ∨ a = gi ∨ a = -gi := by
  have hn := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) a).mpr ha
  obtain ⟨r, s⟩ := a
  simp only [Zsqrtd.norm_def, neg_mul, one_mul, sub_neg_eq_add] at hn
  have hr : -1 ≤ r ∧ r ≤ 1 := by constructor <;> nlinarith [sq_nonneg s]
  have hs : -1 ≤ s ∧ s ≤ 1 := by constructor <;> nlinarith [sq_nonneg r]
  obtain ⟨hr₁, hr₂⟩ := hr
  obtain ⟨hs₁, hs₂⟩ := hs
  interval_cases r <;> interval_cases s <;> norm_num [gi, Zsqrtd.ext_iff] at *

theorem source_law : @Equation1496 ℤ[i] (lin gi (-gi)) := by
  intro x y z
  simp only [lin_op]
  linear_combination x * gi_sq

/-- E1113 has only unit coefficients over the Gaussian integers. -/
theorem coefficients_1113 (a b : ℤ[i]) (h : @Equation1113 ℤ[i] (lin a b)) :
    (a * b) ^ 2 = 1 ∧ (a + b ^ 2) * (1 + a * b) = 0 := by
  constructor
  · have h1 := h 1 0
    simp only [lin_op] at h1
    linear_combination -h1
  · have h2 := h 0 1
    simp only [lin_op] at h2
    linear_combination -h2

/-- The three traps cover every coefficient pair allowed by E1113. -/
theorem traps_1113 (a b : ℤ[i]) (h : @Equation1113 ℤ[i] (lin a b)) :
    Trapped a b := by
  obtain ⟨h1, h2⟩ := coefficients_1113 a b h
  have ha : IsUnit a := isUnit_iff_exists_inv.mpr ⟨a * b ^ 2, by linear_combination h1⟩
  have hb : IsUnit b := isUnit_iff_exists_inv.mpr ⟨a ^ 2 * b, by linear_combination h1⟩
  rcases unit_cases a ha with rfl | rfl | rfl | rfl <;>
    rcases unit_cases b hb with rfl | rfl | rfl | rfl <;>
    revert h1 h2 <;> decide

/-- E680 forces `a*b=1`; its only Gaussian-linear model has `a=b=-1`. -/
theorem traps_680 (a b : ℤ[i]) (h : @Equation680 ℤ[i] (lin a b)) :
    Trapped a b := by
  have h1 : a * b = 1 := by
    have := h 1 0
    simp only [lin_op] at this
    linear_combination -this
  have h2 : a + b ^ 2 * (a ^ 2 + a * b + b) = 0 := by
    have := h 0 1
    simp only [lin_op] at this
    linear_combination -this
  have ha : IsUnit a := isUnit_iff_exists_inv.mpr ⟨b, h1⟩
  have hb : IsUnit b := isUnit_iff_exists_inv.mpr ⟨a, by simpa [mul_comm] using h1⟩
  rcases unit_cases a ha with rfl | rfl | rfl | rfl <;>
    rcases unit_cases b hb with rfl | rfl | rfl | rfl <;>
    revert h1 h2 <;> decide

/-- E1682 also forces both coefficients to be units; the residue traps cover them. -/
theorem traps_1682 (a b : ℤ[i]) (h : @Equation1682 ℤ[i] (lin a b)) :
    Trapped a b := by
  have h1 : a * b * (1 + a + b) = 1 := by
    have := h 1 0
    simp only [lin_op] at this
    linear_combination -this
  have h2 : a ^ 2 + b ^ 2 = 0 := by
    have := h 0 1
    simp only [lin_op] at this
    linear_combination -this
  have ha : IsUnit a := isUnit_iff_exists_inv.mpr ⟨b * (1 + a + b), by linear_combination h1⟩
  have hb : IsUnit b := isUnit_iff_exists_inv.mpr ⟨a * (1 + a + b), by linear_combination h1⟩
  rcases unit_cases a ha with rfl | rfl | rfl | rfl <;>
    rcases unit_cases b hb with rfl | rfl | rfl | rfl <;>
    revert h1 h2 <;> decide

/-- Operations preserving the real axis remain so under taking terms. -/
def PreservesReal (f : ℤ[i] → ℤ[i] → ℤ[i]) : Prop :=
  ∀ x y, x.im = 0 → y.im = 0 → (f x y).im = 0

theorem preservesReal_invariant {N : Magma ℤ[i]} (h : PreservesReal N.op) :
    N.IsCloneInvariant PreservesReal where
  fst := fun _ _ hx _ => hx
  snd := fun _ _ _ hy => hy
  comp := fun _ _ hf hg x y hx hy => h _ _ (hf x y hx hy) (hg x y hx hy)

theorem source_not_real : ¬ PreservesReal (lin gi (-gi)).op := by
  intro h
  have := h 1 0 rfl rfl
  norm_num [lin_op, gi] at this

/-- Reduction of the diagonal modulo a residue prime obstructs recovery. -/
theorem no_recovery_mod_five (a b : ℤ[i]) (φ : ℤ[i] →+* ZMod 5)
    (hφ : φ (a + b) = 1)
    (hback : @Set.TermDefinable ℤ[i] ∅ MagmaLanguage (lin a b).FOStructure
      (Fin 2) (lin gi (-gi)).FinArityOp) : False := by
  have hinv := lin_isCloneInvariant a b (a + b - 1) 1 (by ring)
  obtain ⟨u, v, w, hop, hc⟩ := hinv.of_termDefinable hback
  have hd := hop 1 1
  simp only [lin_op, mul_one, add_neg_cancel] at hd
  have hz : (0 : ℤ[i]) = 1 + (a + b - 1) * w := hd.trans hc
  have hcφ : φ (a + b - 1) = 0 := by rw [map_sub, hφ, map_one, sub_self]
  have hm := congrArg φ hz
  simp only [map_zero, map_add, map_one, map_mul, hcφ, zero_mul, add_zero] at hm
  exact (by decide : (0 : ZMod 5) ≠ 1) hm

theorem no_recovery (a b : ℤ[i]) (h : Trapped a b)
    (hback : @Set.TermDefinable ℤ[i] ∅ MagmaLanguage (lin a b).FOStructure
      (Fin 2) (lin gi (-gi)).FinArityOp) : False := by
  rcases h with ⟨ha, hb⟩ | ha | hb
  · have hreal : PreservesReal (lin a b).op := by
      intro x y hx hy
      simp [lin_op, Zsqrtd.im_add, Zsqrtd.im_mul, ha, hb, hx, hy]
    exact source_not_real ((preservesReal_invariant hreal).of_termDefinable hback)
  · exact no_recovery_mod_five a b gi5a ha hback
  · exact no_recovery_mod_five a b gi5b hb hback

/-- A target whose Gaussian-linear realizations all lie in the traps cannot recover E1496. -/
theorem not_termStructural (L : NatMagmaLaw)
    (hL : ∀ a b, @satisfies _ ℤ[i] (lin a b) L → Trapped a b) :
    ¬ L.TermStructuralFrom Law1496 := by
  intro h
  obtain ⟨N, hN, hfwd, hback⟩ := h (Magma.lin Magma.gi (-Magma.gi))
    ((@Law1496.models_iff GaussianInt (Magma.lin Magma.gi (-Magma.gi))).mpr
      GaussianRecovery.source_law)
  obtain ⟨a, b, _, hop, _⟩ :=
    (Magma.lin_isCloneInvariant Magma.gi (-Magma.gi) (-1) 1 (by ring)).of_termDefinable hfwd
  have hEq : N = Magma.lin a b := by
    cases N
    exact congrArg Magma.mk (funext fun x => funext fun y => hop x y)
  subst N
  exact no_recovery a b (hL a b hN) hback

end GaussianRecovery

theorem Equation1113_not_termStructuralFrom_Equation1496_gaussian :
    ¬ Law1113.TermStructuralFrom Law1496 :=
  GaussianRecovery.not_termStructural Law1113 fun a b h =>
    GaussianRecovery.traps_1113 a b ((@Law1113.models_iff GaussianInt (Magma.lin a b)).mp h)

theorem Equation680_not_termStructuralFrom_Equation1496_gaussian :
    ¬ Law680.TermStructuralFrom Law1496 :=
  GaussianRecovery.not_termStructural Law680 fun a b h =>
    GaussianRecovery.traps_680 a b ((@Law680.models_iff GaussianInt (Magma.lin a b)).mp h)

theorem Equation1682_not_termStructuralFrom_Equation1496_gaussian :
    ¬ Law1682.TermStructuralFrom Law1496 :=
  GaussianRecovery.not_termStructural Law1682 fun a b h =>
    GaussianRecovery.traps_1682 a b ((@Law1682.models_iff GaussianInt (Magma.lin a b)).mp h)

/-- info: 'Equation1113_not_termStructuralFrom_Equation1496_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation1113_not_termStructuralFrom_Equation1496_gaussian

/-- info: 'Equation680_not_termStructuralFrom_Equation1496_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation680_not_termStructuralFrom_Equation1496_gaussian

/-- info: 'Equation1682_not_termStructuralFrom_Equation1496_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation1682_not_termStructuralFrom_Equation1496_gaussian
