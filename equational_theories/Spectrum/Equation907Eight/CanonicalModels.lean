import equational_theories.Spectrum.Equation907Eight.Canonical

namespace Spectrum.E907Eight

namespace Canonical

theorem covers (f : Equiv.Perm (Fin 8)) :
    relabel f 0 = 0 ∧ ∃ g ∈ rows, ∀ x, relabel f (f x) = g (relabel f x) := by
  have hf : f ∈ permsOfList (List.finRange 8) :=
    mem_permsOfList_of_mem (fun _ _ => List.mem_finRange _)
  have hc := List.all_eq_true.mp checked f hf
  simp only [correct, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hc
  obtain ⟨hzero,ht⟩ := hc
  obtain ⟨g,hg,he⟩ := List.mem_map.mp ht
  refine ⟨hzero,g,hg,?_⟩
  intro x
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    (List.map_inj_left.mp he (relabel f x) (List.mem_finRange _)).symm

end Canonical

theorem canonical_model (h : Law907.HasModel 8) :
    ∃ M : Magma (Fin 8), @Equation907 (Fin 8) M ∧
      ∃ g ∈ Canonical.rows, ∀ x, M.op 0 x = g x := by
  obtain ⟨M,hM⟩ := h
  have hE : @Equation907 (Fin 8) M := (@Law907.models_iff _ M).mp hM
  let f : Equiv.Perm (Fin 8) := Equiv.ofBijective (M.op 0)
    ⟨@E907.left_injective _ M _ hE 0, @E907.left_surjective _ M hE 0⟩
  let e := Canonical.relabel f
  obtain ⟨hzero,g,hg,he⟩ := Canonical.covers f
  let N := M.relabel e
  have hzero' : e.symm 0 = 0 := by
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using hzero.symm
  refine ⟨N, ?_, g, hg, ?_⟩
  · apply (@Law907.models_iff _ N).mp
    exact (@Law.satisfies_equiv _ _ _ M N (M.relabelEquiv e) Law907).mp hM
  · intro x
    change e (M.op (e.symm 0) (e.symm x)) = g x
    rw [hzero']
    exact (he (e.symm x)).trans (congrArg g (e.apply_symm_apply x))

end Spectrum.E907Eight
