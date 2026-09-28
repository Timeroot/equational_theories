import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! A product constraint for the row and column profiles of a homogeneous
quasigroup on a finite field. No identity or odd-characteristic assumption is used. -/

namespace Definability.HomogeneousQuasigroup

open Finset
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

lemma product_nonzero : ∏ x ∈ (univ : Finset K).erase 0, x = (-1 : K) := by
  classical
  calc
    _ = ∏ x : Kˣ, (x : K) := by
      apply prod_bij (fun x hx => Units.mk0 x (mem_erase.mp hx).1)
      · intro x hx; exact mem_univ _
      · intro x hx y hy h; exact congrArg Units.val h
      · intro y _; exact ⟨y, by simp, by ext; rfl⟩
      · intro x hx; rfl
    _ = -1 := by
      change (∏ x : Kˣ, (Units.coeHom K) x) = -1
      rw [← map_prod, FiniteField.prod_univ_units_id_eq_neg_one]
      rfl

lemma product_erase_zero (f : K → K) (hf : Function.Bijective f)
    (b : K) (hb : f b = 0) : ∏ x ∈ (univ : Finset K).erase b, f x = -1 := by
  classical
  rw [← product_nonzero (K := K)]
  apply prod_bij (fun x _ => f x)
  · intro x hx
    simp only [mem_erase, mem_univ, and_true] at hx ⊢
    exact fun he => hx (hf.1 (he.trans hb.symm))
  · intro x _ y _ h; exact hf.1 h
  · intro y hy
    obtain ⟨x, hx⟩ := hf.2 y
    refine ⟨x, ?_, hx⟩
    simp only [mem_erase, mem_univ, and_true]
    intro he
    subst x
    exact (mem_erase.mp hy).1 (hx.symm.trans hb)
  · intro x hx; rfl

/-- Multiplying all nonzero entries of both permutation profiles determines
the first entry from the zero's position. -/
theorem zero_product (f : K → K) (c b : K) (hf : Function.Bijective f)
    (hb : b ≠ 0) (hfb : f b = 0)
    (hp : Function.Bijective (fun x => if x = 0 then c else f x / x)) :
    f 0 = -c * b := by
  classical
  let P := ∏ x ∈ ((univ : Finset K).erase b).erase 0, f x
  let Q := ∏ x ∈ ((univ : Finset K).erase b).erase 0, x
  have hP : f 0 * P = -1 := by
    rw [← product_erase_zero f hf b hfb]
    exact mul_prod_erase _ _ (by simp [hb.symm])
  have hQ : b * Q = -1 := by
    rw [← product_nonzero (K := K)]
    dsimp [Q]
    rw [erase_right_comm]
    exact mul_prod_erase (univ.erase (0 : K)) (fun x : K => x) (a := b) (by simp [hb])
  have hQ0 : Q ≠ 0 := by intro h; simp [h] at hQ
  have hprofile : c * (P / Q) = -1 := by
    have hz : (if b = 0 then c else f b / b) = 0 := by simp [hb, hfb]
    have h := product_erase_zero (fun x => if x = 0 then c else f x / x) hp b hz
    rw [← mul_prod_erase ((univ : Finset K).erase b)
      (fun x => if x = 0 then c else f x / x) (a := 0) (by simp [hb.symm])] at h
    simp only at h
    rw [show (∏ x ∈ ((univ : Finset K).erase b).erase 0,
        if x = 0 then c else f x / x) = P / Q by
      rw [← prod_div_distrib]
      apply prod_congr rfl
      intro x hx
      rw [if_neg (mem_erase.mp hx).1]] at h
    exact h
  have hPQ : c * P = -Q := by
    have he : c * P / Q = -1 := by simpa [mul_div_assoc] using hprofile
    simpa using (div_eq_iff hQ0).mp he
  have haQ : f 0 * Q = c := by
    linear_combination f 0 * hPQ - c * hP
  calc
    f 0 = -(f 0) * (b * Q) := by rw [hQ]; ring
    _ = -b * (f 0 * Q) := by ring
    _ = -c * b := by rw [haQ]; ring

/-- Convenient hypotheses for constructing the right profile's bijection. -/
theorem zero_product_of_profiles (f : K → K) (c b : K)
    (hf : Function.Bijective f) (hb : b ≠ 0) (hfb : f b = 0)
    (hsep : ∀ t, t ≠ 0 → f t / t ≠ c)
    (hinj : ∀ t u, t ≠ 0 → u ≠ 0 → f t / t = f u / u → t = u) :
    f 0 = -c * b := by
  classical
  apply zero_product f c b hf hb hfb
  suffices hi : Function.Injective (fun x => if x = 0 then c else f x / x) from
    ⟨hi, Finite.surjective_of_injective hi⟩
  intro x y h
  by_cases hx : x = 0
  · subst x
    by_cases hy : y = 0
    · exact hy.symm
    · simp only [if_neg hy] at h
      exact (hsep y hy h.symm).elim
  · by_cases hy : y = 0
    · subst y
      simp only [if_neg hx] at h
      exact (hsep x hx h).elim
    · simp only [if_neg hx, if_neg hy] at h
      exact hinj x y hx hy h

/-- info: 'Definability.HomogeneousQuasigroup.zero_product_of_profiles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zero_product_of_profiles

end Definability.HomogeneousQuasigroup
