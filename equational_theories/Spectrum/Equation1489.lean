import equational_theories.Spectrum.TransversalGluing1489
import equational_theories.Spectrum.Generated.Idempotent1489Seeds
import equational_theories.Spectrum.Generated.SmallOrder
import equational_theories.Spectrum.Generated.Exclusion1489_4
import equational_theories.Spectrum.Shapes

/-! # The exact spectrum of E1489

Seven-group transversal designs, with two groups truncated, give idempotent
models at every positive order other than 2 and 4. See the complete constructive
argument in `docs/1489_finite_spectrum_theorem.md`.
-/
namespace Spectrum

theorem idempotent_models_1489 (n : ℕ) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    Nonempty (Idempotent1489 (Fin n)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 35
    · exact Idempotent1489.Seeds.exists_small hn h2 h4
    obtain ⟨b,hb,k,hlo,hhi⟩ := TransversalSeven.core_size (by omega : 35 ≤ n)
    obtain ⟨Q,f,⟨D⟩,hc⟩ := TransversalSeven.exists_size hb k
    letI := f
    have hq : 7 ≤ Fintype.card Q := by
      have hb7 : 7 ≤ b := by
        simp only [TransversalSeven.bases, Finset.mem_insert, Finset.mem_singleton] at hb
        omega
      have hp : 0 < 7^k := pow_pos (by omega) k
      rw [hc]
      nlinarith
    rw [← hc] at hlo hhi
    obtain ⟨r,s,hr,hs,hr2,hr4,hs2,hs4,hrs⟩ := TransversalSeven.split_size hq
      (show n - 5 * Fintype.card Q ≤ 2 * Fintype.card Q by omega)
    obtain ⟨M⟩ := ih (Fintype.card Q) (by omega) (by omega) (by omega)
    obtain ⟨R⟩ := ih r (by omega) hr2 hr4
    obtain ⟨S⟩ := ih s (by omega) hs2 hs4
    have he : 5 * Fintype.card Q + r + s = n := by omega
    rw [← he]
    exact D.model_interval hr hs M R S (fun m hm hm7 =>
      Idempotent1489.Seeds.exists_small (by omega) (by omega) (by omega))

theorem models_1489 {n : ℕ} (h2 : n ≠ 2) (h4 : n ≠ 4) : Law1489.HasModel n := by
  obtain ⟨M⟩ := idempotent_models_1489 n h2 h4
  exact ⟨M.magma, (@Law1489.models_iff _ M.magma).mpr M.equation1489⟩

theorem spectrum_1489 : Law1489.spectrum = positiveExcept {2,4} := by
  apply Set.Subset.antisymm
  · rintro n ⟨hn,hM⟩
    refine ⟨hn, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => not_two_1489 (h ▸ hM), fun h => not_order_1489_4 (h ▸ hM)⟩
  · intro n hn
    have h : 0 < n ∧ n ≠ 2 ∧ n ≠ 4 := by simpa [positiveExcept] using hn
    exact ⟨h.1,models_1489 h.2.1 h.2.2⟩

spectrum_assert idempotent_models_1489 complete
spectrum_assert models_1489 complete
spectrum_assert spectrum_1489 complete
end Spectrum
