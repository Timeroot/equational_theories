import equational_theories.Spectrum.MendelsohnTwoHole
import equational_theories.Spectrum.QuasigroupBounds
import equational_theories.Spectrum.Generated.NoteWitnesses

/-! # The complete spectrum of E1719

Bose constructions cover all three residue classes modulo three. The new
shared-two-point construction covers residue two, with order eight supplied
by a checked table. The other exceptional order is six. No design-existence
axiom, native computation, or pending obligation is used in the exact theorem.
-/

namespace Spectrum

/-- A two-point squaring permutation cannot have order three. -/
theorem no_two_1719 : ¬ Law1719.HasModel 2 := by
  rintro ⟨M, hM⟩
  letI := M
  have h := (@Law1719.models_iff _ M).mp hM
  have hs : ∀ x : Fin 2, x ◇ x = x := by
    have small : ∀ s : Fin 2 → Fin 2, (∀ x, s (s (s x)) = x) → ∀ x, s x = x := by decide
    exact small (fun x => x ◇ x) (SemisymmetricTwist.square_three h)
  have hxy (x y : Fin 2) : x = y ◇ (x ◇ y) := by simpa only [hs] using h x y
  have hab : (0 : Fin 2) ◇ 1 = 0 := by
    by_contra hab
    have hab' : (0 : Fin 2) ◇ 1 = 1 := by omega
    have e := hxy 0 1
    rw [hab', hs] at e
    exact (by decide : (0 : Fin 2) ≠ 1) e
  have hba : (1 : Fin 2) ◇ 0 = 0 := by
    simpa only [hab] using (hxy 0 1).symm
  have e := hxy 1 0
  rw [hba, hs] at e
  exact (by decide : (1 : Fin 2) ≠ 0) e

/-- Every positive order except two has an E1719 model. -/
theorem models_1719 {n : ℕ} (hn : 0 < n) (hn2 : n ≠ 2) : Law1719.HasModel n := by
  by_cases h6 : n = 6
  · subst n; exact NoteWitness.model_1719_6
  by_cases h8 : n = 8
  · subst n; exact NoteWitness.model_1719_8
  by_cases hr : n % 3 = 2
  · have hm : 0 < (n-2)/3 := by omega
    have hm2 : (n-2)/3 ≠ 2 := by omega
    have he : 3*((n-2)/3)+2 = n := by omega
    exact he ▸ MendelsohnTwoHole.models hm hm2
  · have hm : n % 3 = 0 ∨ n % 3 = 1 := by omega
    have hp : n ∈ residues 3 {0,1} {6} := by
      simpa only [residues, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
        using And.intro hn (And.intro hm h6)
    exact (mendelsohn_1719 hp).2

/-- Includes the empty model, following the `HasModel` convention. -/
theorem hasModel_1719_iff (n : ℕ) : Law1719.HasModel n ↔ n ≠ 2 := by
  constructor
  · intro h hn; subst n; exact no_two_1719 h
  · intro hn
    by_cases h0 : n = 0
    · subst n; exact Law1719.hasModel_zero
    exact models_1719 (by omega) hn

theorem spectrum_1719 : Law1719.spectrum = positiveExcept {2} := by
  ext n
  simp only [Law.MagmaLaw.mem_spectrum, hasModel_1719_iff, positiveExcept,
    Set.mem_setOf_eq, Finset.mem_singleton]

spectrum_assert no_two_1719 complete
spectrum_assert models_1719 complete
spectrum_assert spectrum_1719 complete
end Spectrum
