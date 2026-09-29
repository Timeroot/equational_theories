import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

/-! The elementary arithmetic behind Wilson's asymptotic constructions.
Multiplicative meshes first give relative density; truncated designs then
turn relative density into bounded additive gaps. -/
namespace Spectrum.PBD.AsymptoticArithmetic

/-- Products of two nearby integers give an eventual multiplicative mesh.
This is Wilson's §20.4 without introducing an explicit infinite sequence. -/
theorem multiplicative_mesh {u v : ℕ} (hu : 1 < u) (huv : u < v) :
    ∃ B : ℕ, ∀ x : ℚ, B ≤ x → ∃ i j : ℕ,
      0 < i+j ∧ x < (u:ℚ)^i*v^j ∧ (u:ℚ)*((u:ℚ)^i*v^j) ≤ v*x := by
  have huq : (1:ℚ) < u := by exact_mod_cast hu
  have hup : (0:ℚ) < u := by positivity
  have huvq : (u:ℚ) < v := by exact_mod_cast huv
  let ρ : ℚ := v/u
  have hρ : 1 < ρ := (one_lt_div hup).mpr huvq
  have hρp : 0 < ρ := by linarith
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (u:ℚ) hρ
  refine ⟨u^N,?_⟩
  intro x hx
  have hxN : (u:ℚ)^N ≤ x := by exact_mod_cast hx
  have hx1 : (1:ℚ) ≤ x := (one_le_pow₀ huq.le).trans hxN
  obtain ⟨n,hn,hnext⟩ := exists_nat_pow_near hx1 huq
  have hNn : N ≤ n := by
    by_contra h
    have hp : (u:ℚ)^(n+1) ≤ (u:ℚ)^N := pow_le_pow_right₀ huq.le (by omega)
    linarith
  have hpow : (0:ℚ) < (u:ℚ)^n := pow_pos hup _
  let z : ℚ := x/(u:ℚ)^n
  have hz1 : 1 ≤ z := (one_le_div hpow).mpr hn
  have hzu : z < u := by
    apply (div_lt_iff₀ hpow).mpr
    simpa only [pow_succ,mul_comm] using hnext
  obtain ⟨t,ht,hzt⟩ := exists_nat_pow_near hz1 hρ
  have htN : t < N := by
    by_contra h
    have hp : ρ^N ≤ ρ^t := pow_le_pow_right₀ hρ.le (by omega)
    linarith
  have hjn : t+1 ≤ n := by omega
  have heq : (u:ℚ)^(n-(t+1))*(v:ℚ)^(t+1) = (u:ℚ)^n*ρ^(t+1) := by
    dsimp [ρ]
    rw [div_pow,← mul_div_assoc,eq_div_iff (pow_ne_zero _ hup.ne')]
    have h := pow_add (u:ℚ) (n-(t+1)) (t+1)
    rw [Nat.sub_add_cancel hjn] at h
    calc
      _ = ((u:ℚ)^(n-(t+1))*(u:ℚ)^(t+1))*(v:ℚ)^(t+1) := by ring
      _ = _ := by rw [← h]
  refine ⟨n-(t+1),t+1,by omega,?_,?_⟩
  · rw [heq]
    have h := mul_lt_mul_of_pos_left hzt hpow
    dsimp [z] at h
    simpa [mul_div_cancel₀ _ hpow.ne'] using h
  · rw [heq]
    have h := mul_le_mul_of_nonneg_left ht hρp.le
    rw [← pow_succ'] at h
    have h' := mul_le_mul_of_nonneg_left h hpow.le
    dsimp [z,ρ] at h'
    have hu0 : (u:ℚ) ≠ 0 := hup.ne'
    have hp0 : (u:ℚ)^n ≠ 0 := hpow.ne'
    field_simp at h' ⊢
    nlinarith

/-- Relative density and the truncated-design operation imply bounded gaps.
Strong induction replaces the sequence argument in Wilson's §20.5. -/
theorem bounded_gaps {C : Set ℕ} {a A B M : ℕ} (ha : 0 < a) (hM : M ∈ C)
    (_hMp : 0 < M) (hMB : (a+1)*B ≤ M)
    (net : ∀ x : ℚ, B ≤ x → ∃ r, r ∈ C ∧ A ≤ r ∧ x < r ∧ (a:ℚ)*r ≤ (a+1)*x)
    (step : ∀ r, r ∈ C → A ≤ r → ∀ t, t ∈ C → t ≤ r → a*r+t ∈ C) :
    ∀ n, ∃ s, s ∈ C ∧ n < s ∧ s ≤ n+M := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnM : n < M
    · exact ⟨M,hM,hnM,by omega⟩
    have han : (0:ℚ) < a+1 := by positivity
    have hnB : (B:ℚ) ≤ (n:ℚ)/(a+1) := by
      apply (le_div_iff₀ han).mpr
      exact_mod_cast (by nlinarith : B*(a+1) ≤ n)
    obtain ⟨r,hr,hrA,hnr,har⟩ := net ((n:ℚ)/(a+1)) hnB
    have hlow : a*r ≤ n := by
      have heq : ((a:ℚ)+1)*((n:ℚ)/(a+1)) = n := mul_div_cancel₀ _ han.ne'
      rw [heq] at har
      exact_mod_cast har
    have hhigh : n < (a+1)*r := by
      have h := (div_lt_iff₀ han).mp hnr
      exact_mod_cast (by nlinarith : (n:ℚ) < (a+1)*r)
    have hrpos : 0 < r := by nlinarith
    let d := n-a*r
    have hd : d < n := by dsimp [d]; have : 0 < a*r := Nat.mul_pos ha hrpos; omega
    have hdeq : a*r+d = n := Nat.add_sub_of_le hlow
    have hd' : d < r := by nlinarith only [hdeq,hhigh]
    obtain ⟨t,ht,hdt,htM⟩ := ih d hd
    have htC : min t r ∈ C := by
      by_cases h : t ≤ r
      · simpa [min_eq_left h] using ht
      · simpa [min_eq_right (by omega : r ≤ t)] using hr
    refine ⟨a*r+min t r,step r hr hrA _ htC (min_le_right _ _),?_,?_⟩
    · have : d < min t r := lt_min hdt hd'
      omega
    · have : min t r ≤ t := min_le_left _ _
      omega

/-- A long finite arithmetic progression, together with bounded gaps, fills
one infinite progression. This is the final arithmetic step of §20.2. -/
theorem progression_tail {C : Set ℕ} {a k A M d : ℕ}
    (ha : 0 < a) (_hk : 0 < k) (hka : k ∣ a) (hkd : k ∣ d)
    (gaps : ∀ n, ∃ s, s ∈ C ∧ n < s ∧ s ≤ n+M)
    (progression : ∀ j, j*k ≤ a*(M+1) → d+j*k ∈ C)
    (step : ∀ s, s ∈ C → A ≤ s → ∀ t, t ∈ C → t ≤ s → a*s+t ∈ C) :
    ∃ N, ∀ n, N ≤ n → k ∣ n → n ∈ C := by
  let H := A+d+a*(M+1)+M+1
  refine ⟨d+a*(H+M+1),?_⟩
  intro n hn hkn
  have hdn : d ≤ n := by omega
  let q := (n-d)/a
  have hq : H+M+1 ≤ q := by
    apply (Nat.le_div_iff_mul_le ha).mpr
    nlinarith only [hn,Nat.sub_add_cancel hdn]
  obtain ⟨s,hs,hqs,hsq⟩ := gaps (q-M)
  have hsle : s ≤ q := by omega
  have hsA : A ≤ s := by dsimp [H] at hq; omega
  have hsd : d+a*(M+1) ≤ s := by dsimp [H] at hq; omega
  have has : a*s ≤ n-d := by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hsle
  let t := n-a*s
  have hst : a*s+t = n := Nat.add_sub_of_le (by omega)
  have htlo : d ≤ t := by dsimp [t]; omega
  have hthi : t ≤ d+a*(M+1) := by
    have hdiv := Nat.mod_add_div (n-d) a
    have hmod := Nat.mod_lt (n-d) ha
    have hmul := Nat.mul_le_mul_left a (show q ≤ s+M from by omega)
    dsimp [q] at hmul
    nlinarith only [hdiv,hmod,hmul,hst,Nat.sub_add_cancel hdn]
  have hkt : k ∣ t := (Nat.dvd_add_iff_right (hka.mul_right s)).mpr (hst ▸ hkn)
  have hdiff : k ∣ t-d := Nat.dvd_sub hkt hkd
  obtain ⟨j,hj⟩ := hdiff
  have ht : t = d+j*k := by rw [Nat.mul_comm] at hj; omega
  have htC : t ∈ C := by rw [ht]; exact progression j (by omega)
  exact hst ▸ step s hs hsA t htC (by omega)

end Spectrum.PBD.AsymptoticArithmetic
