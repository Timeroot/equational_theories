import equational_theories.Spectrum.PBD.Transversal
import Mathlib.Data.Nat.ChineseRemainder

/-! Cyclic transversal designs with an arbitrary number of groups.
Only the primes at most the number of finite slopes need to be avoided. -/
namespace Spectrum.PBD

def smallPrimes (k : ℕ) : Finset ℕ := (Finset.range (k+1)).filter Nat.Prime

@[simp] theorem mem_smallPrimes {p k : ℕ} :
    p ∈ smallPrimes k ↔ p ≤ k ∧ p.Prime := by
  simp [smallPrimes]

def primorial (k : ℕ) : ℕ := ∏ p ∈ smallPrimes k, p

theorem primorial_pos (k : ℕ) : 0 < primorial k :=
  Finset.prod_pos (fun _ h => (mem_smallPrimes.mp h).2.pos)

theorem dvd_primorial {p k : ℕ} (hp : p.Prime) (hk : p ≤ k) : p ∣ primorial k :=
  Finset.dvd_prod_of_mem _ (mem_smallPrimes.mpr ⟨hk, hp⟩)

theorem coprime_small {q d k : ℕ} (hq : q.Coprime (primorial k))
    (hd : 0 < d) (hk : d ≤ k) : q.Coprime d := by
  by_contra h
  obtain ⟨p, hp, hpq, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have hpk : p ≤ k := (Nat.le_of_dvd hd hpd).trans hk
  have hc := hq.of_dvd_right (dvd_primorial hp hpk)
  exact (hp.coprime_iff_not_dvd.mp hc.symm) hpq

private theorem cyclic_units {q k : ℕ} (hq : q.Coprime (primorial k))
    (i j : Fin k) (hij : i ≠ j) : IsUnit ((i.val : ZMod q) - (j.val : ZMod q)) := by
  have hu (a b : Fin k) (h : b.val < a.val) :
      IsUnit ((a.val : ZMod q) - (b.val : ZMod q)) := by
    rw [← Nat.cast_sub (Nat.le_of_lt h)]
    exact (ZMod.isUnit_iff_coprime _ _).mpr
      (coprime_small hq (Nat.sub_pos_of_lt h) (by omega)).symm
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · simpa only [neg_sub] using (hu j i h).neg
  · exact hu i j h

/-- The vertical coordinate and `k` finite slopes over `ZMod q`. -/
theorem HasTD.cyclic {q k : ℕ} (hq : 0 < q) (hc : q.Coprime (primorial k)) :
    HasTD (k+1) q := by
  letI : NeZero q := ⟨by omega⟩
  let D := Transversal.ring (fun i : Fin k => (i.val : ZMod q)) (cyclic_units hc)
  exact ⟨(D.reindex (finSuccEquiv k)).relabel (ZMod.finEquiv q).toEquiv.symm⟩

end Spectrum.PBD
