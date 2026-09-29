import equational_theories.Spectrum.PBD.WilsonPrimePowers

/-! The two design-existence inputs needed by the spectrum cofiniteness
arguments. These are proved from the constructions, without extra axioms. -/
namespace Spectrum.PBD
open Classical

private theorem prime_consecutive {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    (h : p ∣ n*(n-1)) : n%p = 0 ∨ n%p = 1 := by
  rcases hp.dvd_mul.mp h with h | h
  · exact Or.inl (Nat.mod_eq_zero_of_dvd h)
  · right
    have hmod : (n-1)%p = 0 := Nat.mod_eq_zero_of_dvd h
    have heq : n = (n-1)+1 := by omega
    conv_lhs => rw [heq]
    simp [Nat.add_mod,hmod,Nat.mod_eq_of_lt hp.one_lt]

/-- Wilson existence for the E677 seed block sizes. -/
theorem wilson_5_11_16 : WilsonExistence {5,11,16} := by
  let K : Finset ℕ := {5,11,16}
  let C := designClosure (K : Set ℕ)
  have hC : DesignClosed C := designClosure_closed _
  have h5 : 5 ∈ C := subset_designClosure _ (by simp [K])
  have h11 : 11 ∈ C := subset_designClosure _ (by simp [K])
  have h16 : 16 ∈ C := subset_designClosure _ (by simp [K])
  have h1 : 1 ∈ C := one_mem_designClosure _
  have h80 : 80 ∈ C := hC.mul_order h5 h16 (by
    simpa using HasTD.primePower (p := 2) (e := 4) (k := 5) (by decide) (by decide) (by decide))
  have p5 : EventuallyPeriodic C 20 := by
    simpa using hC.eventual_period_primePower (p := 5) (e := 1) (by decide) (by decide) (by simpa using h5)
  have p11 : EventuallyPeriodic C 110 := by
    simpa using hC.eventual_period_primePower (p := 11) (e := 1) (by decide) (by decide) (by simpa using h11)
  have p16 : EventuallyPeriodic C 240 := by
    simpa using hC.eventual_period_primePower (p := 2) (e := 4) (by decide) (by decide) (by simpa using h16)
  have p10 : EventuallyPeriodic C 10 := by simpa using (p5.gcd p11).gcd p16
  have hU : UniformOneTail 5 := by
    simpa using uniform_one_tail_primePower (p := 5) (e := 1) (by decide) (by decide)
  have hF := hC.complete_fibres_of_period (by decide) h5 hU (by decide : 0 < 10) p10
  obtain ⟨N,hN⟩ := hF.finite_seeds {1,5,16,80} (by
    intro s hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨by decide,h1⟩
    · exact ⟨by decide,h5⟩
    · exact ⟨by decide,h16⟩
    · exact ⟨by decide,h80⟩)
  refine ⟨max 1 N,?_⟩
  intro n hn hadm
  have h10 : 10 ∣ n*(n-1) := by
    have h := hadm.2
    rw [show ({5,11,16} : Finset ℕ).gcd (fun k => k*(k-1)) = 10 from by decide] at h
    exact h
  have hr5 := prime_consecutive (by decide : Nat.Prime 5) (by omega)
    ((by decide : 5 ∣ 10).trans h10)
  have cases : n%10 = 0 ∨ n%10 = 1 ∨ n%10 = 5 ∨ n%10 = 6 := by omega
  apply designClosure_finset.mp
  apply hN n (by omega)
  rcases cases with h | h | h | h
  · exact ⟨80,by simp,by change n%10 = 80%10; omega⟩
  · exact ⟨1,by simp,by change n%10 = 1%10; omega⟩
  · exact ⟨5,by simp,by change n%10 = 5%10; omega⟩
  · exact ⟨16,by simp,by change n%10 = 16%10; omega⟩

/-- Wilson existence for the shared E1083/E1286 seed block sizes. -/
theorem wilson_7_9_16 : WilsonExistence {7,9,16} := by
  let K : Finset ℕ := {7,9,16}
  let C := designClosure (K : Set ℕ)
  have hC : DesignClosed C := designClosure_closed _
  have h7 : 7 ∈ C := subset_designClosure _ (by simp [K])
  have h9 : 9 ∈ C := subset_designClosure _ (by simp [K])
  have h16 : 16 ∈ C := subset_designClosure _ (by simp [K])
  have h1 : 1 ∈ C := one_mem_designClosure _
  have h144 : 144 ∈ C := hC.mul_order h9 h16 (by
    simpa using HasTD.primePower (p := 2) (e := 4) (k := 9) (by decide) (by decide) (by decide))
  have p7 : EventuallyPeriodic C 42 := by
    simpa using hC.eventual_period_primePower (p := 7) (e := 1) (by decide) (by decide) (by simpa using h7)
  have p9 : EventuallyPeriodic C 72 := by
    simpa using hC.eventual_period_primePower (p := 3) (e := 2) (by decide) (by decide) (by simpa using h9)
  have p16 : EventuallyPeriodic C 240 := by
    simpa using hC.eventual_period_primePower (p := 2) (e := 4) (by decide) (by decide) (by simpa using h16)
  have p6 : EventuallyPeriodic C 6 := by simpa using (p7.gcd p9).gcd p16
  have hU : UniformOneTail 7 := by
    simpa using uniform_one_tail_primePower (p := 7) (e := 1) (by decide) (by decide)
  have hF := hC.complete_fibres_of_period (by decide) h7 hU (by decide : 0 < 6) p6
  obtain ⟨N,hN⟩ := hF.finite_seeds {1,9,16,144} (by
    intro s hs
    simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨by decide,h1⟩
    · exact ⟨by decide,h9⟩
    · exact ⟨by decide,h16⟩
    · exact ⟨by decide,h144⟩)
  refine ⟨max 1 N,?_⟩
  intro n hn hadm
  have h6 : 6 ∣ n*(n-1) := by
    have h := hadm.2
    rw [show ({7,9,16} : Finset ℕ).gcd (fun k => k*(k-1)) = 6 from by decide] at h
    exact h
  have hr3 := prime_consecutive (by decide : Nat.Prime 3) (by omega)
    ((by decide : 3 ∣ 6).trans h6)
  have cases : n%6 = 0 ∨ n%6 = 1 ∨ n%6 = 3 ∨ n%6 = 4 := by omega
  apply designClosure_finset.mp
  apply hN n (by omega)
  rcases cases with h | h | h | h
  · exact ⟨144,by simp,by change n%6 = 144%6; omega⟩
  · exact ⟨1,by simp,by change n%6 = 1%6; omega⟩
  · exact ⟨9,by simp,by change n%6 = 9%6; omega⟩
  · exact ⟨16,by simp,by change n%6 = 16%6; omega⟩

/-- info: 'Spectrum.PBD.wilson_5_11_16' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms wilson_5_11_16
/-- info: 'Spectrum.PBD.wilson_7_9_16' depends on axioms: [propext, choice, Quot.sound] -/
#guard_msgs in
#print axioms wilson_7_9_16

end Spectrum.PBD
