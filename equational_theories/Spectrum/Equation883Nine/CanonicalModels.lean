import equational_theories.Spectrum.Equation883Nine.Canonical

namespace Spectrum.E883Nine

namespace Canonical

theorem covers (f : Equiv.Perm (Fin 9)) :
    relabel f 0 = 0 ∧ ∃ g ∈ rows, ∀ x, relabel f (f x) = g (relabel f x) := by
  have hf : f ∈ permsOfList (List.finRange 9) :=
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

/-- Every nine-element E883 model has a conjugate whose first row is one
of the 66 nonidentity canonical cycle representatives. -/
theorem canonical_model (h : Law883.HasModel 9) :
    ∃ M : Magma (Fin 9), @Equation883 (Fin 9) M ∧
      ∃ g ∈ Canonical.rows, (∀ x, M.op 0 x = g x) ∧ (∃ x, g x ≠ x) := by
  obtain ⟨M,hM,hn⟩ := normalized_model h
  let f : Equiv.Perm (Fin 9) := Equiv.ofBijective (M.op 0)
    ⟨@E667883.left_injective883 _ M _ hM 0, @E667883.left_surjective883 _ M hM 0⟩
  let e := Canonical.relabel f
  obtain ⟨hzero,g,hg,he⟩ := Canonical.covers f
  let N := M.relabel e
  have hzero' : e.symm 0 = 0 := by
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using hzero.symm
  have hrow : ∀ x, N.op 0 x = g x := by
    intro x
    change e (M.op (e.symm 0) (e.symm x)) = g x
    rw [hzero']
    exact (he (e.symm x)).trans (congrArg g (e.apply_symm_apply x))
  refine ⟨N, ?_, g, hg, hrow, ?_⟩
  · apply (@Law883.models_iff _ N).mp
    exact (@Law.satisfies_equiv _ _ _ M N (M.relabelEquiv e) Law883).mp
      ((@Law883.models_iff _ M).mpr hM)
  · obtain ⟨b,hb⟩ := hn
    refine ⟨e b, ?_⟩
    intro hb'
    have hh : e (M.op 0 b) = e b := (he b).trans hb'
    exact hb (e.injective hh)

end Spectrum.E883Nine
