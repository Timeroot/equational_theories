import equational_theories.Spectrum.PBD.CompleteFibres

/-! Eventual periods for PBD-closed sets containing a prime-power block size. -/
namespace Spectrum.PBD
open Classical

/-- Two consecutive multiples suffice to reduce the constructed periods to
`k(k-1)`; no theorem about primes in arithmetic progressions is needed. -/
theorem DesignClosed.period_of_uniform_tail {C : Set ℕ} (hC : DesignClosed C) {k : ℕ}
    (hk : 2 ≤ k) (hkC : k ∈ C) (hU : UniformOneTail k) :
    EventuallyPeriodic C (k*(k-1)) := by
  obtain ⟨U,hU'⟩ := hU
  let b := k*(k-1)
  have hb : 2 ≤ b := by dsimp [b]; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hp (t : ℕ) (ht : U+1 ≤ t) : EventuallyPeriodic C (b*t) := by
    have hv : 3 ≤ b*t+1 := by nlinarith
    have hvmod : (b*t+1)%b = 1 := by simp [Nat.add_mod,Nat.mod_eq_of_lt hb]
    have hvD : b*t+1 ∈ designClosure {k} := hU' _ (by nlinarith) hvmod
    have h := (hC.complete_fibres hk hkC ⟨U,hU'⟩ hv hvD hvmod).eventuallyPeriodic (by omega)
    simpa only [Nat.add_sub_cancel] using h
  have h := (hp (U+1) le_rfl).gcd (hp (U+2) (by omega))
  have hg : Nat.gcd (b*(U+1)) (b*(U+2)) = b := by
    rw [Nat.gcd_mul_left]
    have hsucc : Nat.gcd (U+1) (U+2) = 1 := by
      have h : U+2 = (U+1)+1 := by omega
      rw [h]
      simp [Nat.gcd_self_add_right]
    rw [hsucc,Nat.mul_one]
  rwa [hg] at h

theorem DesignClosed.eventual_period_primePower {C : Set ℕ} (hC : DesignClosed C) {p e : ℕ}
    (hp : p.Prime) (he : e ≠ 0) (hkC : p^e ∈ C) :
    EventuallyPeriodic C (p^e*(p^e-1)) :=
  hC.period_of_uniform_tail (by have := one_lt_pow₀ hp.one_lt he; omega) hkC
    (uniform_one_tail_primePower hp he)

/-- Eventual periodicity and enlargement of positive seeds imply that every
original occupied fibre is complete, including seeds below the cutoff. -/
theorem DesignClosed.complete_fibres_of_period {C : Set ℕ} (hC : DesignClosed C) {k d : ℕ}
    (hk : 2 ≤ k) (hkC : k ∈ C) (hU : UniformOneTail k) (hd : 0 < d)
    (hp : EventuallyPeriodic C d) : CompleteFibres C d := by
  obtain ⟨N,hN⟩ := hp.same_residue
  intro u hu huC
  obtain ⟨w,hw,hwC,hwu⟩ := hC.large_residue hk hkC hU hd hu huC N
  exact ⟨N,fun n hn hnu => (hN n w hn hw (hnu.trans hwu.symm)).mpr hwC⟩

/-- A finite set of positive seeds supplies a uniform cutoff for its fibres. -/
theorem CompleteFibres.finite_seeds {C : Set ℕ} {d : ℕ} (h : CompleteFibres C d)
    (S : Finset ℕ) (hS : ∀ s ∈ S, 0 < s ∧ s ∈ C) :
    ∃ N, ∀ n, N ≤ n → (∃ s ∈ S, n ≡ s [MOD d]) → n ∈ C := by
  have ht : ∀ s : S, ∃ N, ∀ n, N ≤ n → n ≡ s.val [MOD d] → n ∈ C := by
    intro s
    exact h s.val (hS _ s.property).1 (hS _ s.property).2
  choose A hA using ht
  refine ⟨Finset.univ.sup A,?_⟩
  rintro n hn ⟨s,hs,hns⟩
  exact hA ⟨s,hs⟩ n ((Finset.le_sup (f := A) (Finset.mem_univ ⟨s,hs⟩)).trans hn) hns

end Spectrum.PBD
