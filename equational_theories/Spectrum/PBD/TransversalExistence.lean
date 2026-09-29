import equational_theories.Spectrum.PBD.IdempotentTransversal
import equational_theories.Spectrum.PBD.DesignTruncation
import equational_theories.Spectrum.PBD.Cyclic
import Mathlib.Data.Nat.Factorization.Basic

/-! Eventual existence of transversal designs, following the elementary
Chowla–Erdős–Straus argument in Wilson's thesis, §19.3. -/
namespace Spectrum.PBD
open Classical
namespace HasITD

theorem zero (k : ℕ) : HasITD k 0 := by
  refine ⟨{ line := fun p _ => p.1, pair := ?_, diagonal := fun _ _ => rfl }⟩
  intro i j _
  exact ⟨fun p => Fin.elim0 p.1,fun p => Fin.elim0 p.1⟩

theorem prod {k : ℕ} {I : Type*} (s : Finset I) (f : I → ℕ)
    (h : ∀ i ∈ s, HasITD k (f i)) : HasITD k (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using one k
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- MacNeish's product construction, stated in terms of prime-power factors. -/
theorem of_primePowers {k n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, k ≤ p ^ n.factorization p) : HasITD k n := by
  have heq : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors]
    exact Nat.prod_factorization_pow_eq_self hn
  rw [← heq]
  apply prod
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  exact primePower hprime (hprime.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).ne'
    (h p hp)

theorem of_coprime {k n : ℕ} (hn : n ≠ 0) (hc : n.Coprime (primorial k)) : HasITD k n := by
  apply of_primePowers hn
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  have hpk : k < p := by
    by_contra h
    have h := hc.of_dvd_right (dvd_primorial hprime (by omega))
    exact (hprime.coprime_iff_not_dvd.mp h.symm) hdvd
  exact hpk.le.trans (Nat.le_self_pow (hprime.factorization_pos_of_dvd hn hdvd).ne' _)

theorem of_power_dichotomy {k n e : ℕ} (hn : n ≠ 0) (he : k ≤ 2^e)
    (h : ∀ p, p.Prime → p ≤ k → p ∣ n → p^e ∣ n) : HasITD k n := by
  apply of_primePowers hn
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  by_cases hpk : p ≤ k
  · have hpow := h p hprime hpk hdvd
    have hexp : e ≤ n.factorization p := (hprime.pow_dvd_iff_le_factorization hn).mp hpow
    exact he.trans ((Nat.pow_le_pow_left hprime.two_le e).trans
      (Nat.pow_le_pow_right hprime.pos hexp))
  · exact (by omega : k ≤ p).trans
      (Nat.le_self_pow (hprime.factorization_pos_of_dvd hn hdvd).ne' _)

end HasITD

namespace TransversalExistence

def complementProduct (m n : ℕ) : ℕ :=
  ∏ p ∈ (smallPrimes m).filter (fun p => ¬p ∣ n), p

theorem complementProduct_pos (m n : ℕ) : 0 < complementProduct m n := by
  apply Finset.prod_pos
  intro p hp
  exact (mem_smallPrimes.mp (Finset.mem_filter.mp hp).1).2.pos

theorem complementProduct_dvd (m n : ℕ) : complementProduct m n ∣ primorial m :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

theorem complementProduct_coprime (m n : ℕ) : n.Coprime (complementProduct m n) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  obtain ⟨hp,hpn⟩ := Finset.mem_filter.mp hp
  exact ((mem_smallPrimes.mp hp).2.coprime_iff_not_dvd.mpr hpn).symm

theorem dvd_complementProduct {p m n : ℕ} (hp : p.Prime) (hpm : p ≤ m) (hpn : ¬p ∣ n) :
    p ∣ complementProduct m n :=
  Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨mem_smallPrimes.mpr ⟨hpm,hp⟩,hpn⟩)

/-- Consecutive orders available before using any PBD closure. -/
theorem consecutive (k : ℕ) (hk : 2 ≤ k) :
    ∃ m, k ≤ m ∧ HasITD k m ∧ HasITD k (m+1) ∧ m.Coprime (primorial k) := by
  let P := primorial k
  have hP : 2 ≤ P := Nat.le_of_dvd (primorial_pos k) (dvd_primorial Nat.prime_two hk)
  let m := P^(k+1)-1
  have hpow : 0 < P^(k+1) := pow_pos (by omega) _
  have hm : m+1 = P^(k+1) := Nat.sub_add_cancel (by omega)
  have hmlo : k ≤ m := by
    have h := Nat.lt_pow_self (a := P) (n := k+1) (by omega)
    omega
  have hcop : m.Coprime P := by
    have hcop' : (m+1).Coprime m := by simp [Nat.coprime_self_add_left]
    rw [hm] at hcop'
    exact ((Nat.coprime_pow_left_iff (Nat.succ_pos k) P m).mp hcop').symm
  refine ⟨m,hmlo,HasITD.of_coprime (by omega) hcop,?_,hcop⟩
  rw [hm]
  apply HasITD.of_power_dichotomy (by positivity) (show k ≤ 2^(k+1) by have := Nat.lt_pow_self (n := k+1) (a := 2) (by decide); omega)
  intro p hp _ hdvd
  exact pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hdvd) _

/-- Split every sufficiently large order into the two group fillings in the
truncated-transversal construction. The complementary prime product makes
one filling free of small prime factors and makes the other's small factors
occur to sufficiently high powers. -/
theorem decompose {k m : ℕ} (hk : 2 ≤ k) (hkm : k ≤ m)
    (hcop : m.Coprime (primorial k)) :
    ∃ N, ∀ n, N ≤ n → ∃ a b,
      a ≤ b ∧ m*b+a = n ∧ HasITD k a ∧ HasITD (m+1) b := by
  let M := (primorial (m+1))^(m+1)
  have hM : 0 < M := pow_pos (primorial_pos _) _
  have hm : 0 < m := by omega
  have hmM : 0 < m*M := Nat.mul_pos hm hM
  refine ⟨(2*m+2)*(m*M),?_⟩
  intro n hn
  let C := (complementProduct (m+1) n)^(m+1)
  have hC : 0 < C := pow_pos (complementProduct_pos _ _) _
  have hCM : C ∣ M := pow_dvd_pow_of_dvd (complementProduct_dvd _ _) _
  have hCle : C ≤ M := Nat.le_of_dvd hM hCM
  let t := n/(m*M)-1
  have hq : 2*m+2 ≤ n/(m*M) := (Nat.le_div_iff_mul_le hmM).mpr hn
  have ht : n/(m*M) = t+1 := by dsimp [t]; omega
  let b := t*M+C
  let a := n%(m*M)+m*(M-C)
  have ha_bound : a < 2*(m*M) := by
    have hmod := Nat.mod_lt n hmM
    have hmul := Nat.mul_le_mul_left m (Nat.sub_le M C)
    dsimp [a]
    omega
  have hb_bound : 2*(m*M) ≤ b := by
    have ht' : 2*m ≤ t := by omega
    have hmul := Nat.mul_le_mul_right M ht'
    dsimp [b]
    nlinarith
  have hbpos : 0 < b := by omega
  have heq : m*b+a = n := by
    have hc : C+(M-C) = M := Nat.add_sub_of_le hCle
    have hmul := congrArg (fun z => m*z) hc
    calc
      m*b+a = n%(m*M)+(m*M)*(t+1) := by dsimp [a,b]; nlinarith
      _ = n := by rw [← ht]; exact Nat.mod_add_div n (m*M)
  have hMpow (p : ℕ) (hp : p.Prime) (hpm : p ≤ m+1) : p^(m+1) ∣ M :=
    pow_dvd_pow_of_dvd (dvd_primorial hp hpm) _
  have hMdiv (p : ℕ) (hp : p.Prime) (hpm : p ≤ m+1) : p ∣ M :=
    (dvd_pow_self p (by omega : m+1 ≠ 0)).trans (hMpow p hp hpm)
  have hbnot (p : ℕ) (hp : p.Prime) (hpm : p ≤ m+1) (hpn : p ∣ n) : ¬p ∣ b := by
    intro hpb
    have hpC : p ∣ C := (Nat.dvd_add_iff_right ((hMdiv p hp hpm).mul_left t)).mpr hpb
    have hc := (complementProduct_coprime (m+1) n).pow_right (m+1)
    exact ((hp.coprime_iff_not_dvd.mp (hc.of_dvd_left hpn)) hpC)
  have hbpow (p : ℕ) (hp : p.Prime) (hpm : p ≤ m+1) (hpn : ¬p ∣ n) : p^(m+1) ∣ b :=
    Nat.dvd_add ((hMpow p hp hpm).mul_left t)
      (pow_dvd_pow_of_dvd (dvd_complementProduct hp hpm hpn) _)
  have hbdesign : HasITD (m+1) b := by
    apply HasITD.of_power_dichotomy hbpos.ne'
      (show m+1 ≤ 2^(m+1) from (Nat.lt_pow_self (by decide)).le)
    intro p hp hpm hpb
    exact hbpow p hp hpm (fun hpn => hbnot p hp hpm hpn hpb)
  have hadesign : HasITD k a := by
    by_cases ha : a = 0
    · simpa [ha] using HasITD.zero k
    apply HasITD.of_coprime ha
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    obtain ⟨hpk,hprime⟩ := mem_smallPrimes.mp hp
    apply Nat.Coprime.symm
    apply hprime.coprime_iff_not_dvd.mpr
    intro hpa
    have hpm : p ≤ m+1 := by omega
    by_cases hpn : p ∣ n
    · have hpmb : p ∣ m*b := (Nat.dvd_add_iff_left hpa).mpr (heq ▸ hpn)
      have hpm' : ¬p ∣ m := (hprime.coprime_iff_not_dvd.mp
        (hcop.of_dvd_right (dvd_primorial hprime hpk)).symm)
      exact hbnot p hprime hpm hpn ((hprime.dvd_mul.mp hpmb).resolve_left hpm')
    · have hpb : p ∣ b := (dvd_pow_self p (by omega : m+1 ≠ 0)).trans (hbpow p hprime hpm hpn)
      exact hpn (heq ▸ Nat.dvd_add (hpb.mul_left m) hpa)
  exact ⟨a,b,by omega,heq,hadesign,hbdesign⟩

/-- Chowla–Erdős–Straus: every sufficiently large order admits any fixed
number of mutually orthogonal idempotent coordinates. -/
theorem eventual_idempotent (k : ℕ) (hk : 2 ≤ k) :
    ∃ N, ∀ n, N ≤ n → HasITD k n := by
  obtain ⟨m,hkm,hm,hm',hcop⟩ := consecutive k hk
  obtain ⟨N,hN⟩ := decompose hk hkm hcop
  refine ⟨N,?_⟩
  intro n hn
  obtain ⟨a,b,hab,heq,ha,hb⟩ := hN n hn
  have hb' : HasITD k b := by
    obtain ⟨D⟩ := hb
    exact ⟨D.restrictIndex ⟨Fin.castLE (by omega),Fin.castLE_injective _⟩⟩
  have h := (HasITD.closed k).oneHole hb.toHasTD (e := 0) (by omega) hab
    (by simpa using hb') (by simpa using ha) hm hm'
  simpa [heq] using h

end TransversalExistence

/-- For each number of groups, transversal designs exist at every sufficiently
large group order. No design-existence theorem is assumed in this proof. -/
theorem HasTD.eventual (k : ℕ) : ∃ N, ∀ n, N ≤ n → HasTD k n := by
  obtain ⟨N,hN⟩ := TransversalExistence.eventual_idempotent (k+2) (by omega)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨D⟩ := hN n hn
  exact ⟨D.toTransversal.restrictIndex ⟨Fin.castLE (by omega),Fin.castLE_injective _⟩⟩

end Spectrum.PBD
