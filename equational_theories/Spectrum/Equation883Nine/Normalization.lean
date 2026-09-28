import equational_theories.Spectrum.Equation667883Small.Basic

namespace Spectrum.E883Nine

/-- A quasigroup on a nontrivial carrier has a nonidentity left translation. -/
theorem exists_nonidentity_left {A : Type*} [Magma A] [Nontrivial A]
    (h : Equation883 A) : ∃ a b : A, a ◇ b ≠ b := by
  by_contra! hall
  obtain ⟨a,c,hac⟩ := exists_pair_ne A
  exact hac (E667883.right_injective883 h a ((hall a a).trans (hall c a).symm))

/-- Choose a nonidentity left translation as the row labelled zero. -/
theorem normalized_model (h : Law883.HasModel 9) :
    ∃ M : Magma (Fin 9), @Equation883 (Fin 9) M ∧ ∃ b, M.op 0 b ≠ b := by
  obtain ⟨M,hM⟩ := h
  letI := M
  have hE : Equation883 (Fin 9) := (@Law883.models_iff _ M).mp hM
  obtain ⟨a,b,hab⟩ := exists_nonidentity_left hE
  let e := Equiv.swap a (0 : Fin 9)
  let N := M.relabel e
  refine ⟨N, ?_, e b, ?_⟩
  · apply (@Law883.models_iff _ N).mp
    exact (@Law.satisfies_equiv _ _ _ M N (M.relabelEquiv e) Law883).mp hM
  · change e (M.op (e.symm 0) (e.symm (e b))) ≠ e b
    rw [Equiv.symm_apply_apply]
    have he : e.symm 0 = a := Equiv.swap_apply_right a 0
    rw [he]
    exact fun hh => hab (e.injective hh)

end Spectrum.E883Nine
