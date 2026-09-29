import equational_theories.Spectrum.PBD.WeightedSum
import equational_theories.Spectrum.PBD.ReplicationDensity

/-! Wilson's complete fibre at 1 for uniform designs, proved from an
unbounded initial family rather than a general design-existence theorem. -/
namespace Spectrum.PBD.Replication
open Classical
variable {k : ℕ}

/-- §20.7: arbitrarily long progressions of replication numbers, with step k. -/
theorem long_progressions (hk : 2 ≤ k)
    (hu : ∀ N, ∃ v, N ≤ v ∧ v ∈ designClosure {k}) :
    ∀ n, ∃ d, k ∣ d ∧ ∀ j, j ≤ n → d+j*k ∈ replications k := by
  obtain ⟨a,ha,hka,haC,haC',hbC,hbC'⟩ := rectangle hk hu
  have hC := closed hk
  obtain ⟨h,hh,hH,hH',hA,hA',hB,hB'⟩ := six_hole_ingredients hC (by omega) (by omega)
    haC haC' hbC hbC' (unbounded hk hu)
  let H := a*h
  have hkH : k ∣ H := hka.mul_right h
  obtain ⟨A,hAtd⟩ := HasTD.eventual (H+2)
  intro n
  induction n with
  | zero =>
    refine ⟨a,hka,?_⟩
    intro j hj
    have : j = 0 := by omega
    simpa [this] using haC
  | succ n ih =>
    obtain ⟨d,hkd,hd⟩ := ih
    obtain ⟨t,ht,htC⟩ := unbounded hk hu (A+d+n*k+1)
    let d' := H*t+d+a
    refine ⟨d',Nat.dvd_add (Nat.dvd_add (hkH.mul_right t) hkd) hka,?_⟩
    intro j hj
    by_cases hjn : j ≤ n
    · have hjk : j*k ≤ n*k := Nat.mul_le_mul_right k hjn
      have h := hC.weighted_sum hH hH' haC hA hA' htC (hd j hjn)
        (by omega) (by omega) (hAtd t (by omega))
      convert h using 1
      dsimp [d',H]
      ring
    · have hj' : j = n+1 := by omega
      subst j
      have h := hC.weighted_sum hH hH' hbC hB hB' htC (hd n le_rfl)
        (by omega) (by omega) (hAtd t (by omega))
      convert h using 1
      dsimp [d',H]
      ring

/-- The full progression of sufficiently large replication numbers divisible
by k. This is the conclusion of Wilson's §20.2 in replication coordinates. -/
theorem zero_tail (hk : 2 ≤ k)
    (hu : ∀ N, ∃ v, N ≤ v ∧ v ∈ designClosure {k}) :
    ∃ N, ∀ r, N ≤ r → k ∣ r → r ∈ replications k := by
  obtain ⟨a,ha,hka,haC,haC',_⟩ := rectangle hk hu
  obtain ⟨M,hM⟩ := bounded_gaps hk hu (by omega) haC haC'
  obtain ⟨d,hkd,hd⟩ := long_progressions hk hu (a*(M+1))
  obtain ⟨A,hA⟩ := HasTD.eventual (a+1)
  apply AsymptoticArithmetic.progression_tail (by omega) (by omega) hka hkd hM
  · intro j hj
    exact hd j ((Nat.le_mul_of_pos_right j (by omega : 0 < k)).trans hj)
  · intro s hs hsA t ht hts
    have h := (closed hk).oneHole (hA s hsA) (e := 0) (by omega) hts
      (by simpa using hs) (by simpa using ht) haC haC'
    simpa using h

/-- Uniform designs eventually exist at every order congruent to 1 modulo
`k(k-1)`. The sole hypothesis is an unbounded initial family of k-designs. -/
theorem uniform_one_tail (hk : 2 ≤ k)
    (hu : ∀ N, ∃ v, N ≤ v ∧ v ∈ designClosure {k}) :
    ∃ C, ∀ n, C ≤ n → n % (k*(k-1)) = 1 → n ∈ designClosure {k} := by
  obtain ⟨N,hN⟩ := zero_tail hk hu
  let b := k*(k-1)
  have hb : 0 < b := Nat.mul_pos (by omega) (by omega)
  refine ⟨b*(N+1)+1,?_⟩
  intro n hn hmod
  let t := n/b
  have ht : N ≤ t := by
    apply (Nat.le_div_iff_mul_le hb).mpr
    nlinarith
  have hr : k*t ∈ replications k := hN _
    (ht.trans (Nat.le_mul_of_pos_left t (by omega))) (dvd_mul_right k t)
  have heq : (k-1)*(k*t)+1 = n := by
    have h := Nat.mod_add_div n b
    rw [hmod] at h
    dsimp [b,t] at *
    nlinarith only [h]
  change (k-1)*(k*t)+1 ∈ designClosure {k} at hr
  rwa [heq] at hr

end Spectrum.PBD.Replication

namespace Spectrum.PBD
/-- The prime-power instances of Wilson's uniform complete-fibre theorem. -/
theorem uniform_one_tail_primePower {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    ∃ C, ∀ n, C ≤ n → n % (p^e*(p^e-1)) = 1 → n ∈ designClosure {p^e} :=
  Replication.uniform_one_tail (by have := one_lt_pow₀ hp.one_lt he; omega)
    (uniform_unbounded_primePower hp he)
end Spectrum.PBD
