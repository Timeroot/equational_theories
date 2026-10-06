import equational_theories.Spectrum.SmallPairs.OrderEleven.Canonical
import equational_theories.Spectrum.SmallPairs.OrderEleven.Certificates

namespace Spectrum.SmallPairs.OrderEleven

theorem not_hasModel : ¬ Law1313.HasModel 11 := by
  rintro ⟨M, hM⟩
  obtain ⟨f, hf, hd, hc⟩ := normalized M.op ((holds_iff .e1313 M).mpr hM)
  obtain ⟨he0, r, hr, he⟩ := covers (f 0) (left_bijective hf 0).1 hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  let e := relabel (f 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he0.symm
  let g (x y : Fin 11) := e (f (e.symm x) (e.symm y))
  have hg : Holds .e1313 g := holds_relabel hf e
  have hrow : g 0 = row i := by
    funext y
    simpa only [g, he', e, Equiv.apply_symm_apply] using he (e.symm y)
  have hdg : g 0 0 = 0 → ∀ x, g x x = x := by
    intro h0 x
    have hz : f 0 0 = 0 := by
      apply e.injective
      simpa only [g, he', e, he0] using h0
    simp only [g, hd hz, Equiv.apply_symm_apply]
  apply no_model_of_unsat g hg hdg
  · simpa only [hrow] using row_chain i
  · rw [hrow]
    exact unsat i

end Spectrum.SmallPairs.OrderEleven

namespace Spectrum
theorem not_order_1313_11 : ¬ Law1313.HasModel 11 := SmallPairs.OrderEleven.not_hasModel
spectrum_assert not_order_1313_11 complete
end Spectrum
