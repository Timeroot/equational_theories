import equational_theories.Definability.CloneTraps
import equational_theories.Definability.E63Family
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp

/-!
# E125 cannot recover its operation from an E3548 term interpretation

Choose `1<a<2` with `a(1-a)^2=1`, and put `x*y=a*x+(1-a)*y` on the reals.
This satisfies E125. Every binary term remains affine with coefficient sum one.
If such an operation satisfies E3548, its first coefficient `b` satisfies
`b=(1-b)(b²+1-b)`. Since `b²+1-b>0`, this forces `0≤b≤1`.
Thus it preserves `[0,1]`, as does every term formed from it. The original
operation sends `(1,0)` to `a>1`, so no term can recover it.

The obstruction is to term-structural interpretation on arbitrary carriers.
Finite term-structural interpretation and arbitrary-carrier FO-structural
interpretation are both proved elsewhere.
-/

open Law Law.MagmaLaw
namespace E125Convex

@[reducible] def mix (a : ℝ) : Magma ℝ := ⟨fun x y => a*x+(1-a)*y⟩

theorem exists_coefficient : ∃ a : ℝ, 1 < a ∧ a < 2 ∧ a*(1-a)^2 = 1 := by
  have hc : Continuous (fun a : ℝ => a*(1-a)^2) := by fun_prop
  have hi := intermediate_value_Icc (a := (1 : ℝ)) (b := 2) (by norm_num) hc.continuousOn
  obtain ⟨a, ha, he⟩ := hi (by norm_num : (1 : ℝ) ∈ Set.Icc ((1 : ℝ)*(1-1)^2) ((2 : ℝ)*(1-2)^2))
  refine ⟨a, ?_, ?_, he⟩
  · rcases ha.1.eq_or_lt with h | h
    · subst a; norm_num at he
    · exact h
  · rcases ha.2.eq_or_lt with h | h
    · subst a; norm_num at he
    · exact h

theorem equation125 (a : ℝ) (ha : a*(1-a)^2=1) : @Equation125 ℝ (mix a) := by
  intro x y
  change x = a*y+(1-a)*(a*(a*y+(1-a)*x)+(1-a)*y)
  calc
    x = (a*(1-a)^2)*x+(1-a*(1-a)^2)*y := by rw [ha]; ring
    _ = _ := by ring

def Affine (u : ℝ → ℝ → ℝ) : Prop := ∃ a : ℝ, ∀ x y, u x y = a*x+(1-a)*y

theorem affine_invariant (a : ℝ) : (mix a).IsCloneInvariant Affine where
  fst := ⟨1, by intro x y; ring⟩
  snd := ⟨0, by intro x y; ring⟩
  comp f g hf hg := by
    obtain ⟨b,hb⟩ := hf
    obtain ⟨c,hc⟩ := hg
    refine ⟨a*b+(1-a)*c, fun x y => ?_⟩
    change a*(f x y)+(1-a)*(g x y)=_
    rw [hb,hc]
    ring

theorem coefficient_bounds {a : ℝ} (h : @Equation3548 ℝ (mix a)) : 0 ≤ a ∧ a ≤ 1 := by
  have hh := h 1 0
  change a*1+(1-a)*0 = a*0+(1-a)*(a*(a*1+(1-a)*0)+(1-a)*1) at hh
  norm_num at hh
  have hpos : 0 < a*a+(1-a) := by nlinarith [sq_nonneg (a-1/2)]
  constructor
  · by_contra hn
    have hn : a < 0 := lt_of_not_ge hn
    have hp : 0 ≤ (1-a)*(a*a+(1-a)) := mul_nonneg (by linarith) hpos.le
    nlinarith
  · by_contra hn
    have hn : 1 < a := lt_of_not_ge hn
    have hp : (1-a)*(a*a+(1-a)) < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
    nlinarith

def PreservesInterval (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ x y, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ u x y ∧ u x y ≤ 1

theorem mix_preserves {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) : PreservesInterval (mix a).op := by
  intro x y hx hx' hy hy'
  change 0 ≤ a*x+(1-a)*y ∧ a*x+(1-a)*y ≤ 1
  constructor
  · exact add_nonneg (mul_nonneg ha.1 hx) (mul_nonneg (by linarith [ha.2]) hy)
  · have h1 := mul_le_mul_of_nonneg_left hx' ha.1
    have h2 := mul_le_mul_of_nonneg_left hy' (sub_nonneg.mpr ha.2)
    nlinarith

theorem interval_invariant {N : Magma ℝ} (hN : PreservesInterval N.op) :
    N.IsCloneInvariant PreservesInterval where
  fst := by intro x y hx hx' _ _; exact ⟨hx,hx'⟩
  snd := by intro x y _ _ hy hy'; exact ⟨hy,hy'⟩
  comp f g hf hg := by
    intro x y hx hx' hy hy'
    exact hN _ _ (hf x y hx hx' hy hy').1 (hf x y hx hx' hy hy').2
      (hg x y hx hx' hy hy').1 (hg x y hx hx' hy hy').2

theorem no_recovery (a : ℝ) (ha : 1 < a) :
    ¬ Law3548.TermStructuralOnMagma (mix a) := by
  rintro ⟨N, hN, hforward, hback⟩
  obtain ⟨b, hb⟩ := (affine_invariant a).of_termDefinable hforward
  have heq : N = mix b := by
    cases N
    congr 1
    funext x y
    exact hb x y
  subst N
  have hb := coefficient_bounds ((@Law3548.models_iff ℝ (mix b)).mp hN)
  have hp := (interval_invariant (mix_preserves hb)).of_termDefinable hback
  have hh := hp 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change 0 ≤ a*1+(1-a)*0 ∧ a*1+(1-a)*0 ≤ 1 at hh
  norm_num at hh
  linarith [hh.2]

end E125Convex

/-- The real affine witness rules out every reversible term interpretation,
although right division supplies an FO-structural interpretation. -/
theorem Equation3548_not_termStructuralFrom_Equation125_convex :
    ¬ Law3548.TermStructuralFrom Law125 := by
  obtain ⟨a, ha, _, he⟩ := E125Convex.exists_coefficient
  intro h
  exact E125Convex.no_recovery a ha
    (h (E125Convex.mix a) ((@Law125.models_iff ℝ (E125Convex.mix a)).mpr
      (E125Convex.equation125 a he)))

spectrum_assert Equation3548_not_termStructuralFrom_Equation125_convex complete

spectrum_assert E125Convex.exists_coefficient complete
spectrum_assert E125Convex.coefficient_bounds complete
spectrum_assert E125Convex.no_recovery complete
