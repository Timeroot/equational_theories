import equational_theories.Spectrum.PBD.Replication
import equational_theories.Spectrum.PBD.TransversalExistence

/-! The initial four replication numbers in Wilson's argument. Prime-power
block sizes supply the unbounded initial designs through affine geometry. -/
namespace Spectrum.PBD
open Classical PairDecomposition

theorem DesignClosed.mul_order {K : Set ℕ} (hK : DesignClosed K) {k q : ℕ}
    (hk : k ∈ K) (hq : q ∈ K) (D : HasTD k q) : k*q ∈ K := by
  simpa using hK.truncate (k := k) (h := 0) (q := q) (e := 0) (by simpa using D)
    (by omega) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) (by simpa using hq)
    (fun j => Fin.elim0 j) (fun n hlo hhi => by
      have hn : n = k := by omega
      simpa [hn] using hk)

theorem DesignClosed.common_point {K : Set ℕ} (hK : DesignClosed K) {k q : ℕ}
    (hk : k ∈ K) (hq : q+1 ∈ K) (D : HasTD k q) : k*q+1 ∈ K := by
  simpa using hK.truncate (k := k) (h := 0) (q := q) (e := 1) (by simpa using D)
    (by omega) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) hq
    (fun j => Fin.elim0 j) (fun n hlo hhi => by
      have hn : n = k := by omega
      simpa [hn] using hk)

theorem uniform_affine_powers {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) (d : ℕ) :
    (p^e)^d ∈ designClosure {p^e} := by
  induction d with
  | zero => simpa using one_mem_designClosure ({p^e} : Set ℕ)
  | succ d ih =>
    by_cases hd : d = 0
    · subst d
      simpa using subset_designClosure ({p^e} : Set ℕ) (show p^e ∈ ({p^e} : Set ℕ) from rfl)
    have hD : HasTD (p^e) ((p^e)^d) := by
      rw [← pow_mul]
      apply HasTD.primePower hp (Nat.mul_ne_zero he hd)
      have hpow : p^e ≤ p^(e*d) := Nat.pow_le_pow_right hp.pos (Nat.le_mul_of_pos_right e (by omega))
      omega
    have h := (designClosure_closed ({p^e} : Set ℕ)).mul_order
      (subset_designClosure _ rfl) ih hD
    simpa [pow_succ,Nat.mul_comm] using h

/-- Only this supply of initial designs depends on the block size being a
prime power. The subsequent asymptotic argument is combinatorial. -/
theorem uniform_unbounded_primePower {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    ∀ N, ∃ v, N ≤ v ∧ v ∈ designClosure {p^e} := by
  intro N
  refine ⟨(p^e)^(N+1),?_,uniform_affine_powers hp he _⟩
  have hk : 1 < p^e := one_lt_pow₀ hp.one_lt he
  have := Nat.lt_pow_self (n := N+1) hk
  omega

namespace Replication
variable {k : ℕ}

/-- Count the groups obtained by localizing a uniform design. -/
theorem of_uniform {v : ℕ} (_hk : 2 ≤ k) (hv : 0 < v)
    (h : v ∈ designClosure {k}) : ∃ r, v = (k-1)*r+1 ∧ r ∈ replications k := by
  obtain ⟨D⟩ := h
  let o : Fin v := ⟨0,hv⟩
  let r := Nat.card (LocalGroups D o)
  have hs (b : LocalGroups D o) : Nat.card (LocalGroup D o b) = k-1 := by
    rw [card_localGroup]
    exact congrArg (fun n => n-1) (D.sizes _ b.val.property)
  have ht := card_localPoints D o
  rw [Nat.card_fin] at ht
  have ht' : Nat.card (Σ b : LocalGroups D o, LocalGroup D o b) = r*(k-1) := by
    letI := Fintype.ofFinite (LocalGroups D o)
    rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
    simp only [Fintype.card_eq_nat_card,hs,Finset.sum_const,Finset.card_univ,smul_eq_mul]
    rfl
  have heq : v = (k-1)*r+1 := by
    rw [ht'] at ht
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ v)]
  refine ⟨r,heq,?_⟩
  change (k-1)*r+1 ∈ designClosure {k}
  rw [← heq]
  exact ⟨D⟩

theorem unbounded (hk : 2 ≤ k)
    (hu : ∀ N, ∃ v, N ≤ v ∧ v ∈ designClosure {k}) :
    ∀ N, ∃ r, N ≤ r ∧ r ∈ replications k := by
  intro N
  obtain ⟨v,hv,hD⟩ := hu ((k-1)*N+1)
  obtain ⟨r,hr,hR⟩ := of_uniform hk (by omega) hD
  refine ⟨r,?_,hR⟩
  have : 0 < k-1 := by omega
  nlinarith

/-- Wilson's initial rectangle: `a,a+1,a+k,a+k+1` are replication numbers,
with `a` a positive multiple of `k`. -/
theorem rectangle (hk : 2 ≤ k)
    (hu : ∀ N, ∃ v, N ≤ v ∧ v ∈ designClosure {k}) :
    ∃ a, 2 ≤ a ∧ k ∣ a ∧ a ∈ replications k ∧ a+1 ∈ replications k ∧
      a+k ∈ replications k ∧ a+k+1 ∈ replications k := by
  obtain ⟨N,hN⟩ := HasTD.eventual k
  obtain ⟨v,hv,hvC⟩ := hu (N+k+2)
  obtain ⟨t,ht,_⟩ := of_uniform hk (by omega) hvC
  have htpos : 0 < t := by
    by_contra h
    have hz : t = 0 := by omega
    simp [hz] at ht
    omega
  have hvsub : v-1 = (k-1)*t := by omega
  let C := designClosure ({k} : Set ℕ)
  have hC : DesignClosed C := designClosure_closed _
  have hkC : k ∈ C := subset_designClosure _ rfl
  let u := k*(v-1)+1
  let w := k*v
  have huC : u ∈ C := hC.common_point hkC (by rw [Nat.sub_add_cancel (by omega : 1 ≤ v)]; exact hvC) (hN _ (by omega))
  have hwC : w ∈ C := hC.mul_order hkC hvC (hN _ (by omega))
  have huN : N+1 ≤ u := by dsimp [u]; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ v)]
  have hwN : N+1 ≤ w := by dsimp [w]; nlinarith
  have h1 := hC.common_point hkC (by simpa using huC) (hN (u-1) (by omega))
  have h2 := hC.mul_order hkC huC (hN u (by omega))
  have h3 := hC.common_point hkC (by rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]; exact hwC) (hN (w-1) (by omega))
  have h4 := hC.mul_order hkC hwC (hN w (by omega))
  let a := k*k*t
  refine ⟨a,by dsimp [a]; nlinarith,⟨k*t,by dsimp [a]; ring⟩,?_,?_,?_,?_⟩
  · change (k-1)*a+1 ∈ C
    convert h1 using 1
    dsimp [a,u]
    simp only [hvsub]
    ring
  · change (k-1)*(a+1)+1 ∈ C
    convert h2 using 1
    dsimp [a,u]
    rw [hvsub]
    have hkm : k-1+1 = k := by omega
    nlinarith
  · change (k-1)*(a+k)+1 ∈ C
    convert h3 using 1
    have hw : w-1+1 = w := by omega
    dsimp [a,w] at *
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  · change (k-1)*(a+k+1)+1 ∈ C
    convert h4 using 1
    dsimp [a,w]
    nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ k)]

end Replication
end Spectrum.PBD
