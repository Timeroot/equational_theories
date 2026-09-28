import equational_theories.Spectrum.PBD.Transversal

/-! The explicit induction after the finite interval certificate. -/
namespace Spectrum.QuarticTail
open PBD

private theorem cyclic_units (q : ℕ) (hq : q.Coprime 30030)
    (i j : Fin 16) (hij : i ≠ j) :
    IsUnit ((i.val : ZMod q) - (j.val : ZMod q)) := by
  have hu (k : ℕ) (hk : k ∣ 30030^3) : IsUnit (k : ZMod q) :=
    (ZMod.isUnit_iff_coprime k q).mpr ((hq.pow_right 3).symm.of_dvd_left hk)
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | norm_num
  all_goals exact hu _ (by decide)

/-- Sixteen finite slopes and the vertical coordinate over the cyclic ring. -/
theorem cyclic17 {q : ℕ} (hq : 0 < q) (hc : q.Coprime 30030) : HasTD 17 q := by
  letI : NeZero q := ⟨by omega⟩
  let D := Transversal.ring (fun i : Fin 16 => (i.val : ZMod q)) (cyclic_units q hc)
  exact ⟨(D.reindex (finSuccEquiv 16)).relabel (ZMod.finEquiv q).toEquiv.symm⟩

/-- The constants avoid an additional finite search for short coprime gaps. -/
theorem decompose {C n : ℕ} (hC : 0 < C) (hn : 17*C+272*30031 ≤ n) :
    ∃ q r : ℕ, C ≤ q ∧ C ≤ r ∧ q < n ∧ r < n ∧ r ≤ q ∧
      q.Coprime 30030 ∧ 16*q+r=n := by
  let q := 30030*(n/510510+1)+1
  let r := n-16*q
  have hc : q.Coprime 30030 := by
    change (30030*(n/510510+1)+1).Coprime 30030
    rw [Nat.add_comm, Nat.coprime_add_mul_left_left]
    decide
  refine ⟨q,r,?_,?_,?_,?_,?_,hc,?_⟩ <;> dsimp [r,q] <;> omega

end Spectrum.QuarticTail
