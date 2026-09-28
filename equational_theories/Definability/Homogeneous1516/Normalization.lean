import equational_theories.Definability.GLTwo1516
import equational_theories.Definability.Cancel1516

/-! Normalizing homogeneous finite-field models of E1516 to one row and its inverse. -/

namespace Definability.Homogeneous1516

open Law Law.MagmaLaw GLTwo1516

variable {K : Type} [Field K]

/-- The one-row constraints used by the finite homogeneous classification. -/
structure Normalized (f g : K → K) (c s : K) : Prop where
  s_ne_zero : s ≠ 0
  c_ne_zero : c ≠ 0
  f_zero_ne_zero : f 0 ≠ 0
  f_one : f 1 = s
  gf : ∀ t, g (f t) = t
  fg : ∀ t, f (g t) = t
  zero_left : c * f (f 0) = 1
  zero_right : c * c / s = g 0
  main : ∀ t, t ≠ 0 → f (f t) = (s * t) * g ((s * t)⁻¹)
  profile_ne : ∀ t, t ≠ 0 → f t / t ≠ c
  profile_injective : ∀ t u, t ≠ 0 → u ≠ 0 → f t / t = f u / u → t = u

lemma zero_zero {p : K → K → K} (hp : Homogeneous p) (h2 : (2 : K) ≠ 0) :
    p 0 0 = 0 := by
  have hh := hp (-1) 0 0 (neg_ne_zero.mpr one_ne_zero)
  simp only [mul_zero, neg_one_mul] at hh
  have hz : (2 : K) * p 0 0 = 0 := by linear_combination hh
  exact (mul_eq_zero.mp hz).resolve_left h2

lemma zero_row {p : K → K → K} (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (y : K) : p 0 y = p 0 1 * y := by
  by_cases hy : y = 0
  · simp [hy, zero_zero hp h2]
  · simpa [mul_comm] using hp y 0 1 hy

lemma diagonal {p : K → K → K} (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (x : K) : p x x = p 1 1 * x := by
  by_cases hx : x = 0
  · simp [hx, zero_zero hp h2]
  · simpa [mul_comm] using hp x 1 1 hx

lemma row {p : K → K → K} (hp : Homogeneous p) (x y : K) (hx : x ≠ 0) :
    p x y = x * p 1 (y / x) := by
  simpa only [mul_one, mul_div_cancel₀ y hx] using hp x 1 (y / x) hx

variable [Finite K]

omit [Field K] in
lemma left_injective {p : K → K → K}
    (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) (a : K) :
    Function.Injective (p a) := by
  let M : Magma K := ⟨p⟩
  have hM : @satisfies _ K M Law1516 := (@Law1516.models_iff K M).mpr hlaw
  exact injLeft_Equation1516 K M hM a

omit [Field K] in
lemma right_injective {p : K → K → K}
    (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) (b : K) :
    Function.Injective (fun a => p a b) := by
  let M : Magma K := ⟨p⟩
  have hM : @satisfies _ K M Law1516 := (@Law1516.models_iff K M).mpr hlaw
  exact injRight_Equation1516 K M hM b

lemma square_ne_zero {p : K → K → K} (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) : p 1 1 ≠ 0 := by
  let M : Magma K := ⟨p⟩
  have hM : @satisfies _ K M Law1516 := (@Law1516.models_iff K M).mpr hlaw
  obtain ⟨x, hx⟩ := sqSurj_Equation1516 M hM 1
  change p x x = 1 at hx
  rw [diagonal hp h2] at hx
  intro hs
  simp [hs] at hx

lemma square_ne_neg_one {p : K → K → K} (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) : p 1 1 ≠ -1 := by
  intro hs
  have hd (x : K) : p x x = -x := by rw [diagonal hp h2, hs, neg_one_mul]
  have hi : ∀ x, p x x = x := square_involution_idempotent p hlaw
    (fun a _ _ h => left_injective hlaw a h)
    (by
      intro x y
      rw [hd (p x y), hd x, hd y]
      simpa only [neg_one_mul] using
        (hp (-1) x y (neg_ne_zero.mpr one_ne_zero)).symm)
    (by intro x; rw [hd (p x x), hd x, neg_neg])
  have he := hi 1
  rw [hs] at he
  exact h2 (by linear_combination -he)

/-- Every homogeneous E1516 operation yields the normalized finite constraints. -/
theorem exists_normalized {p : K → K → K} (hp : Homogeneous p) (h2 : (2 : K) ≠ 0)
    (hlaw : ∀ x y, x = p (p y y) (p x (p x y))) :
    ∃ g : K → K, Normalized (p 1) g (p 0 1) (p 1 1) := by
  let f : K → K := p 1
  have hf : Function.Bijective f :=
    ⟨left_injective hlaw 1, Finite.surjective_of_injective (left_injective hlaw 1)⟩
  let e : K ≃ K := Equiv.ofBijective f hf
  let g : K → K := e.symm
  have hgf (t : K) : g (f t) = t := e.symm_apply_apply t
  have hfg (t : K) : f (g t) = t := e.apply_symm_apply t
  have hs := square_ne_zero hp h2 hlaw
  have h00 := zero_zero hp h2
  have hc : p 0 1 ≠ 0 := by
    intro h
    exact one_ne_zero (left_injective hlaw 0 (h.trans h00.symm))
  have hf0 : p 1 0 ≠ 0 := by
    intro h
    exact one_ne_zero (right_injective hlaw 0 (h.trans h00.symm))
  have hprofile (t : K) (ht : t ≠ 0) : p 1 t / t = p t⁻¹ 1 := by
    rw [row hp _ _ (inv_ne_zero ht)]
    simp [div_eq_mul_inv, mul_comm]
  refine ⟨g, hs, hc, hf0, rfl, hgf, hfg, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hlaw 1 0
    rw [h00, zero_row hp h2] at h
    exact h.symm
  · have h := hlaw 0 1
    rw [zero_row hp h2, row hp _ _ hs] at h
    have hz : p 1 (p 0 1 * p 0 1 / p 1 1) = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left hs
    exact (hgf (p 0 1 * p 0 1 / p 1 1)).symm.trans (congrArg g hz)
  · intro t ht
    have hst : p 1 1 * t ≠ 0 := mul_ne_zero hs ht
    have h := hlaw 1 t
    rw [diagonal hp h2, row hp _ _ hst] at h
    have he : p 1 (p 1 (p 1 t) / (p 1 1 * t)) = (p 1 1 * t)⁻¹ := by
      apply (mul_left_cancel₀ hst)
      rw [← h, mul_inv_cancel₀ hst]
    have hg : p 1 (p 1 t) / (p 1 1 * t) = g ((p 1 1 * t)⁻¹) :=
      (hgf _).symm.trans (congrArg g he)
    calc
      p 1 (p 1 t) = (p 1 1 * t) * (p 1 (p 1 t) / (p 1 1 * t)) :=
        (mul_div_cancel₀ _ hst).symm
      _ = _ := congrArg (fun z => (p 1 1 * t) * z) hg
  · intro t ht he
    rw [hprofile t ht] at he
    exact (inv_ne_zero ht) (right_injective hlaw 1 he)
  · intro t u ht hu he
    rw [hprofile t ht, hprofile u hu] at he
    exact inv_injective (right_injective hlaw 1 he)

namespace Normalized

variable {f g : K → K} {c s : K} (h : Normalized f g c s)
include h
omit [Finite K]

lemma bijective : Function.Bijective f :=
  ⟨Function.LeftInverse.injective h.gf, Function.RightInverse.surjective h.fg⟩

lemma zero_right_apply : f (c * c / s) = 0 := by rw [h.zero_right, h.fg]

lemma zero_left_inv : f (f 0) = c⁻¹ := by
  apply mul_left_cancel₀ h.c_ne_zero
  rw [h.zero_left, mul_inv_cancel₀ h.c_ne_zero]

lemma main_apply (t : K) (ht : t ≠ 0) :
    f ((s * t)⁻¹ * f (f t)) = (s * t)⁻¹ := by
  rw [h.main t ht, ← mul_assoc, inv_mul_cancel₀ (mul_ne_zero h.s_ne_zero ht), one_mul,
    h.fg]

end Normalized

/-- info: 'Definability.Homogeneous1516.exists_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_normalized

/-- info: 'Definability.Homogeneous1516.square_ne_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms square_ne_neg_one

end Definability.Homogeneous1516
