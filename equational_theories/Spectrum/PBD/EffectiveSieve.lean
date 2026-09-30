import equational_theories.Spectrum.PBD.Cyclic

/-! Integer-weighted finite sieves for effective transversal-design bounds.
The weights are certificates: their construction does not enter the proof. -/
namespace Spectrum.PBD.EffectiveSieve
open Classical

/-- If the total weight of all forbidden sets is smaller than the available
weight, a positive-weight candidate avoids every forbidden set. -/
theorem weighted_avoid {I P : Type*} (s : Finset I) (primes : Finset P)
    (w : I → ℕ) (bad : P → I → Prop) [∀ p i, Decidable (bad p i)] (cap : P → ℕ)
    (bounds : ∀ p ∈ primes, (∑ i ∈ s, if bad p i then w i else 0) ≤ cap p)
    (enough : (∑ p ∈ primes, cap p) < ∑ i ∈ s, w i) :
    ∃ i ∈ s, 0 < w i ∧ ∀ p ∈ primes, ¬bad p i := by
  by_contra hn
  have cover : ∀ i ∈ s, w i ≤ ∑ p ∈ primes, if bad p i then w i else 0 := by
    intro i hi
    by_cases hw : w i = 0
    · simp [hw]
    have hb : ∃ p ∈ primes, bad p i := by
      by_contra h
      exact hn ⟨i, hi, by omega, by simpa using h⟩
    obtain ⟨p, hp, hpi⟩ := hb
    have h := Finset.single_le_sum (f := fun p => if bad p i then w i else 0)
      (fun _ _ => Nat.zero_le _) hp
    simpa only [if_pos hpi] using h
  have hsum := Finset.sum_le_sum cover
  rw [Finset.sum_comm] at hsum
  have hcaps := Finset.sum_le_sum bounds
  omega

/-- Along an arithmetic progression with step coprime to `p`, the candidates
divisible by `p` occupy a single residue class of the progression indices. -/
theorem affine_avoid {I : Type*} (s : Finset I) (primes : Finset ℕ)
    (w index q : I → ℕ) (cap : ℕ → ℕ) (a step : ℕ)
    (progression : ∀ i ∈ s, q i + step * index i = a)
    (coprime : ∀ p ∈ primes, p.Coprime step)
    (bounds : ∀ p ∈ primes, ∀ r,
      (∑ i ∈ s, if index i % p = r then w i else 0) ≤ cap p)
    (enough : (∑ p ∈ primes, cap p) < ∑ i ∈ s, w i) :
    ∃ i ∈ s, 0 < w i ∧ ∀ p ∈ primes, ¬p ∣ q i := by
  classical
  apply weighted_avoid s primes w (fun p i => p ∣ q i) cap ?_ enough
  intro p hp
  change (∑ i ∈ s, if p ∣ q i then w i else 0) ≤ cap p
  by_cases hex : ∃ j ∈ s, p ∣ q j
  · obtain ⟨j, hj, hqj⟩ := hex
    have residue (i : I) (hi : i ∈ s) (hqi : p ∣ q i) :
        index i % p = index j % p := by
      have mod_eq (t : I) (ht : t ∈ s) (hqt : p ∣ q t) :
          step * index t ≡ a [MOD p] := by
        have h := hqt.modEq_zero_nat.add (Nat.ModEq.refl (step * index t))
        simpa only [progression t ht, zero_add] using h.symm
      exact Nat.ModEq.cancel_left_of_coprime (coprime p hp)
        ((mod_eq i hi hqi).trans (mod_eq j hj hqj).symm)
    apply le_trans (Finset.sum_le_sum (fun i hi => ?_)) (bounds p hp (index j % p))
    by_cases hd : p ∣ q i
    · simp only [if_pos hd, if_pos (residue i hi hd), le_refl]
    · simp only [if_neg hd, Nat.zero_le]
  · have hz : (∑ i ∈ s, if p ∣ q i then w i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [if_neg (fun h => hex ⟨i, hi, h⟩)]
    rw [hz]
    exact Nat.zero_le _

/-- The small primes not already excluded by choosing orders congruent to one
modulo six. -/
def primes80 : Finset ℕ :=
  {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79}

theorem primes80_coprime : ∀ p ∈ primes80, p.Coprime 6 := by decide

theorem td81 {q : ℕ} (hq : 0 < q) (hq6 : q % 6 = 1)
    (avoid : ∀ p ∈ primes80, ¬p ∣ q) : HasTD 81 q := by
  apply HasTD.cyclic hq
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  have hp' := (mem_smallPrimes.mp hp).2
  apply Nat.Coprime.symm
  apply hp'.coprime_iff_not_dvd.mpr
  have cases : p = 2 ∨ p = 3 ∨ p ∈ primes80 := by
    have h : ∀ p ∈ smallPrimes 80, p = 2 ∨ p = 3 ∨ p ∈ primes80 := by decide
    exact h p hp
  rcases cases with rfl | rfl | hp80
  · omega
  · omega
  · exact avoid p hp80

end Spectrum.PBD.EffectiveSieve
