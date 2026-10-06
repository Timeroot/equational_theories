import equational_theories.Spectrum.SmallPairs.OrderThirteen.Canonical
import equational_theories.Spectrum.SmallPairs.OrderThirteen.Certificates

namespace Spectrum.SmallPairs.OrderThirteen

theorem not_hasModel : ¬ Law1279.HasModel 13 := by
  rintro ⟨M, hM⟩
  obtain ⟨f, hf, hd, hc⟩ := normalized M.op ((holds_iff .e1279 M).mpr hM)
  obtain ⟨he0, r, hr, he⟩ := covers (f 0) (left_bijective hf 0).1 hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  let e := relabel (f 0)
  have he' : e.symm 0 = 0 := by apply e.injective; simpa using he0.symm
  let g (x y : Fin 13) := e (f (e.symm x) (e.symm y))
  have hg : Holds .e1279 g := holds_relabel hf e
  have hrow : g 0 = row i := by
    funext y
    simpa only [g, he', e, Equiv.apply_symm_apply] using he (e.symm y)
  have hdg : g 0 0 = 0 → ∀ x, g x x = x := by
    intro h0 x
    have hz : f 0 0 = 0 := by
      apply e.injective
      simpa only [g, he', e, he0] using h0
    simp only [g, hd hz, Equiv.apply_symm_apply]
  -- Use the remaining symmetry of the first row to normalize two more cells.
  let d := reduction i (g 1 1) (g 1 0)
  obtain ⟨hd0, hd1, hcomm, hz, ht⟩ := reduction_checked i (g 1 1) (g 1 0)
  change d 0 = 0 at hd0
  change d 1 = 1 at hd1
  change ∀ x, d (row i x) = row i (d x) at hcomm
  have hd0' : d.symm 0 = 0 := by apply d.injective; simpa using hd0.symm
  have hd1' : d.symm 1 = 1 := by apply d.injective; simpa using hd1.symm
  let u (x y : Fin 13) := d (g (d.symm x) (d.symm y))
  have hu : Holds .e1279 u := holds_relabel hg d
  have hru : u 0 = row i := by
    funext x
    simp only [u, hd0', hrow, hcomm, Equiv.apply_symm_apply]
  have hdu : u 0 0 = 0 → ∀ x, u x x = x := by
    intro h0 x
    have hz0 : g 0 0 = 0 := by
      apply d.injective
      simpa only [u, hd0', hd0] using h0
    simp only [u, hdg hz0, Equiv.apply_symm_apply]
  apply no_model_of_unsat i u hu hdu hru
  · simpa only [u, hd1', d] using hz
  · simpa only [u, hd1', hd0', d] using ht
  · exact unsat i

end Spectrum.SmallPairs.OrderThirteen

namespace Spectrum
theorem not_order_1279_13 : ¬ Law1279.HasModel 13 := SmallPairs.OrderThirteen.not_hasModel
spectrum_assert not_order_1279_13 complete
end Spectrum
