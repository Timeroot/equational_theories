import equational_theories.Spectrum.PBD.Cyclic

/-! The arithmetic part of extending a restricted spectrum to all residues.
There is no asymptotic design-existence assumption in this file. -/
namespace Spectrum.PBD.ResidueFilling
open scoped Nat

private theorem unit_residue {p k g n : ℕ}
    (hp : p.Prime) (hg : g.Prime) (hpg : p ≠ g)
    (hpk : p ≤ k) (hgk : g ≤ k) (hkg : k.Coprime g) (hgn : ¬ g ∣ n) :
    ∃ a < primorial k, a.Coprime (primorial k) ∧
      a ≡ 1 [MOD p] ∧ k*a ≡ n [MOD g] := by
  letI : Fact g.Prime := ⟨hg⟩
  have hk0 : (k : ZMod g) ≠ 0 := by
    exact (ZMod.isUnit_iff_coprime k g).mpr hkg |>.ne_zero
  have hn0 : (n : ZMod g) ≠ 0 := by
    intro h
    have hh : n ≡ 0 [MOD g] := (ZMod.natCast_eq_natCast_iff n 0 g).mp (by simpa using h)
    exact hgn (Nat.modEq_zero_iff_dvd.mp hh)
  let s : ZMod g := (n : ZMod g) / (k : ZMod g)
  have hs : s ≠ 0 := div_ne_zero hn0 hk0
  let residues (r : ℕ) := if r = g then s.val else 1
  have hz : ∀ r ∈ smallPrimes k, r ≠ 0 := fun _ h => (mem_smallPrimes.mp h).2.ne_zero
  have hpair : Set.Pairwise (smallPrimes k) Nat.Coprime := by
    intro a ha b hb hab
    exact (Nat.coprime_primes (mem_smallPrimes.mp ha).2 (mem_smallPrimes.mp hb).2).mpr hab
  let a := Nat.chineseRemainderOfFinset residues (fun r => r) (smallPrimes k) hz hpair
  have ha (r : ℕ) (hr : r ∈ smallPrimes k) : (a : ℕ) ≡ residues r [MOD r] := a.property r hr
  have hag : ((a : ℕ) : ZMod g) = s := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (ha g (mem_smallPrimes.mpr ⟨hgk,hg⟩))
    simpa [residues] using h
  refine ⟨a, Nat.chineseRemainderOfFinset_lt_prod _ _ hz hpair, ?_, ?_, ?_⟩
  · apply Nat.coprime_prod_right_iff.mpr
    intro r hr
    by_cases he : r = g
    · subst r
      apply Nat.Coprime.symm
      apply hg.coprime_iff_not_dvd.mpr
      intro h
      have hz' := (ZMod.natCast_eq_natCast_iff _ _ g).mpr h.modEq_zero_nat
      exact hs (hag.symm.trans (by simpa using hz'))
    · have h : (a : ℕ) ≡ 1 [MOD r] := by simpa [residues, he] using ha r hr
      exact Nat.coprime_of_mul_modEq_one 1 (by simpa using h)
  · simpa [residues, hpg] using ha p (mem_smallPrimes.mpr ⟨hpk,hp⟩)
  · apply (ZMod.natCast_eq_natCast_iff _ _ g).mp
    push_cast
    rw [hag]
    dsimp [s]
    field_simp

/-- Congruent naturals have the same coprimality with the modulus. -/
private theorem coprime_of_modEq {q a m : ℕ} (h : q ≡ a [MOD m])
    (ha : a.Coprime m) : q.Coprime m := by
  change Nat.gcd q m = 1
  rw [Nat.gcd_comm q m, Nat.gcd_rec, h, ← Nat.gcd_rec, Nat.gcd_comm]
  exact ha

/-- A whole arithmetic progression of valid transversal-design orders.
The prime-power factor handles target orders divisible by the exceptional prime. -/
theorem progression {p k g e n : ℕ}
    (hp : p.Prime) (hg : g.Prime) (hpg : p ≠ g)
    (hpk : p ≤ k) (hgk : g ≤ k) (hkg : k.Coprime g)
    (he : e ≠ 0) (hpow : k ≤ g^e) (hpowp : g^e ≡ 1 [MOD p]) :
    ∃ a d : ℕ, 0 < d ∧ d ≤ g^e * primorial k ∧ a < d ∧
      ∀ q : ℕ, 0 < q → q ≡ a [MOD d] →
        q ≡ 1 [MOD p] ∧ k*q ≡ n [MOD g] ∧ HasTD (k+1) q := by
  have hM := primorial_pos k
  have hG : 0 < g^e := pow_pos hg.pos _
  have hpM : p ∣ primorial k := dvd_primorial hp hpk
  have hgM : g ∣ primorial k := dvd_primorial hg hgk
  by_cases hgn : g ∣ n
  · refine ⟨g^e, g^e * primorial k, Nat.mul_pos hG hM, le_rfl, ?_, ?_⟩
    · have hMp : p ≤ primorial k := Nat.le_of_dvd hM hpM
      have hp2 := hp.two_le
      nlinarith
    · intro q hq hqa
      have hGq : g^e ∣ q := Nat.modEq_zero_iff_dvd.mp
        ((hqa.of_mul_right (primorial k)).trans Nat.modulus_modEq_zero)
      let Q := q / g^e
      have hqQ : g^e * Q = q := Nat.mul_div_cancel' hGq
      have hQ : Q ≡ 1 [MOD primorial k] :=
        Nat.ModEq.mul_left_cancel' (Nat.ne_of_gt hG) (by simpa only [mul_one, hqQ] using hqa)
      have hQpos : 0 < Q := by nlinarith
      have hgp : g ∣ g^e := dvd_pow_self _ he
      refine ⟨?_, ?_, ?_⟩
      · have h := hpowp.mul (hQ.of_dvd hpM)
        simpa only [hqQ, mul_one] using h
      · exact ((hgp.trans hGq).mul_left k).modEq_zero_nat.trans hgn.zero_modEq_nat
      · rw [← hqQ]
        exact (HasTD.primePower hg he (by omega)).mul
          (HasTD.cyclic hQpos (coprime_of_modEq hQ (Nat.coprime_one_left _)))
  · obtain ⟨a, ha, hc, hap, hag⟩ := unit_residue hp hg hpg hpk hgk hkg hgn
    refine ⟨a, primorial k, hM, ?_, ha, ?_⟩
    · nlinarith
    · intro q hq hqa
      exact ⟨(hqa.of_dvd hpM).trans hap,
        ((hqa.of_dvd hgM).mul_left k).trans hag,
        HasTD.cyclic hq (coprime_of_modEq hqa hc)⟩

private theorem bounded_congruent {d a : ℕ} (hd : 0 < d) (ha : a < d) (b : ℕ) :
    ∃ q : ℕ, b < q ∧ q ≤ b+2*d ∧ q ≡ a [MOD d] := by
  refine ⟨a+d*(b/d+1), ?_, ?_, ?_⟩
  · have hr := Nat.mod_lt b hd
    have he := Nat.mod_add_div b d
    nlinarith
  · have he := Nat.mod_add_div b d
    have hr := Nat.zero_le (b % d)
    nlinarith
  · simp [Nat.ModEq, Nat.add_mod]

/-- An explicit bound relative to the (possibly unknown) restricted-tail cutoff. -/
def cutoff (k g e C : ℕ) : ℕ :=
  (k+1)*(g*C + 2*k*(g^e * primorial k) + C+1)

/-- Split every sufficiently large order in the missing residue as `k*q+g*t`.
Both `q` and `t` are in residue one; `g*t ≤ q` permits the truncated group. -/
theorem decompose {p k g e C n : ℕ}
    (hp : p.Prime) (hg : g.Prime) (hpg : p ≠ g)
    (hpk : p ≤ k) (hgk : g ≤ k) (hkg : k.Coprime g) (hpkdiv : p ∣ k)
    (he : e ≠ 0) (hpow : k ≤ g^e) (hpowp : g^e ≡ 1 [MOD p])
    (hn : cutoff k g e C ≤ n) (hnp : n ≡ g [MOD p]) :
    ∃ q t : ℕ, C ≤ q ∧ C ≤ t ∧ 0 < q ∧
      q ≡ 1 [MOD p] ∧ t ≡ 1 [MOD p] ∧
      g*t ≤ q ∧ k*q+g*t=n ∧ HasTD (k+1) q := by
  obtain ⟨a,d,hd,hdD,ha,hprogress⟩ := progression hp hg hpg hpk hgk hkg he hpow hpowp (n := n)
  obtain ⟨q,hbq,hqb,hqa⟩ := bounded_congruent hd ha (n/(k+1))
  let D := g^e * primorial k
  have hb : g*C+2*k*D+C+1 ≤ n/(k+1) := by
    apply (Nat.le_div_iff_mul_le (show 0 < k+1 by omega)).mpr
    simpa [cutoff, D, Nat.mul_comm] using hn
  have hbmul := Nat.div_mul_le_self n (k+1)
  have hnmod := Nat.mod_lt n (show 0 < k+1 by omega)
  have hndiv := Nat.mod_add_div n (k+1)
  have hqC : C ≤ q := by omega
  have hqpos : 0 < q := by omega
  have hkq : k*q ≤ n := by
    have hqbound : q ≤ n/(k+1)+2*D := by dsimp [D]; omega
    nlinarith
  have hrem : g*C ≤ n-k*q := by
    have hqbound : q ≤ n/(k+1)+2*D := by dsimp [D]; omega
    have heq := Nat.sub_add_cancel hkq
    nlinarith
  have hremq : n-k*q ≤ q := by
    have heq := Nat.sub_add_cancel hkq
    nlinarith
  obtain ⟨hqp,hqg,hD⟩ := hprogress q hqpos hqa
  have hgr : g ∣ n-k*q := (Nat.modEq_iff_dvd' hkq).mp hqg
  let t := (n-k*q)/g
  have hgt : g*t = n-k*q := Nat.mul_div_cancel' hgr
  have htC : C ≤ t := by
    apply (Nat.le_div_iff_mul_le hg.pos).mpr
    simpa only [Nat.mul_comm] using hrem
  have hsum : k*q+g*t=n := by omega
  have htp : t ≡ 1 [MOD p] := by
    have hz : k*q ≡ 0 [MOD p] := (hpkdiv.mul_right q).modEq_zero_nat
    have hh : g*t ≡ n [MOD p] := by
      have h := hz.add (Nat.ModEq.refl (g*t))
      simpa only [hsum, zero_add] using h.symm
    apply Nat.ModEq.cancel_left_of_coprime ((Nat.coprime_primes hp hg).mpr hpg)
    simpa only [mul_one] using hh.trans hnp
  exact ⟨q,t,hqC,htC,hqpos,hqp,htp,by omega,hsum,hD⟩

end Spectrum.PBD.ResidueFilling
