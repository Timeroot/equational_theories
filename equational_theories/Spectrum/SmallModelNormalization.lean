import equational_theories.Spectrum.Basic

open Law Law.MagmaLaw
namespace Spectrum.Symmetry

/-- Relabel a model so that the square of a chosen element is itself or a second label. -/
theorem two_label_model (L : NatMagmaLaw) {n : ℕ} (h : L.HasModel n)
    (a b : Fin n) (hab : a ≠ b) :
    ∃ M : Magma (Fin n), @satisfies _ (Fin n) M L ∧ (M.op a a = a ∨ M.op a a = b) := by
  obtain ⟨M, hM⟩ := h
  by_cases ha : M.op a a = a
  · exact ⟨M, hM, Or.inl ha⟩
  let p := Equiv.swap b (M.op a a)
  have hpa : p a = a := Equiv.swap_apply_of_ne_of_ne hab (Ne.symm ha)
  refine ⟨M.relabel p, (@satisfies_equiv _ _ _ M (M.relabel p) (M.relabelEquiv p) L).mp hM, Or.inr ?_⟩
  change p (M.op (p.symm a) (p.symm a)) = b
  have hp : p.symm a = a := by simpa [p] using hpa
  rw [hp]
  exact Equiv.swap_apply_right b (M.op a a)

end Spectrum.Symmetry
