import equational_theories.Spectrum.Equation1076.OrderTwelve.Semantic
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.C0
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.C1G234
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.C2G234
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.C3G2345
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.C4G23456
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.C5G234
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.C5G567
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.C5G891011
import equational_theories.Spectrum.Equation1076.OrderTwelve.Certificates.Coverage
import Mathlib.Tactic.FinCases

/-! No E1076 magma has twelve elements. First exclude the three translation
cycle types containing a three-cycle. Their nonexistence strengthens the
remaining three cases. All finite-data refutations are checked in Lean. -/
namespace Spectrum.E1076.OrderTwelve
open SmallOrders CanonicalData RowTransfer PointEncoding Semantic

private theorem early_row (j : Fin 6) (hj : j.val < 3)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hm : Matches f (row (representative j))) : False := by
  fin_cases j
  · exact no_row _ false Certificates.C0.unsat f h hm (chain_checked 0) (by simp)
  · obtain ⟨g,hg,hgm,hp⟩ := normalize_point 1 f h hm
    exact no_group _ false [2,3,4] Certificates.C1G234.unsat g hg hgm
      (chain_checked 1) (by simp) hp
  · obtain ⟨g,hg,hgm,hp⟩ := normalize_point 2 f h hm
    exact no_group _ false [2,3,4] Certificates.C2G234.unsat g hg hgm
      (chain_checked 2) (by simp) hp
  all_goals simp at hj

/-- An order-specific consequence, proved before using it in the later CNFs.
It is not valid at all orders: affine E1076 models at order thirteen can have
three-cycles in their left translations. -/
theorem no_three (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f) : NoThree f := by
  intro x y hxy hcyc
  obtain ⟨g,e,hg,he,hrel,hc⟩ := normalize_at f h x
  obtain ⟨i,hm⟩ := exists_row Certificates.Coverage.unsat g hg hc
  by_cases hi : (target i).val < 3
  · exact transfer_row i (fun q hq hqm => early_row (target i) hi q hq hqm) g hg hm
  · have hz : e y ≠ 0 := by
      intro hy
      exact hxy (e.injective (he.trans hy.symm))
    have hc' : g 0 (g 0 (g 0 (e y))) = e y := by
      rw [← he,hrel,hrel,hrel,hcyc]
    have hr : row i (row i (row i (e y))) = e y := by simpa only [hm] using hc'
    exact late_no_three i (by omega) (e y) hz hr

private theorem all_rows (j : Fin 6)
    (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f)
    (hm : Matches f (row (representative j))) : False := by
  fin_cases j
  · exact early_row 0 (by decide) f h hm
  · exact early_row 1 (by decide) f h hm
  · exact early_row 2 (by decide) f h hm
  · obtain ⟨g,hg,hgm,hp⟩ := normalize_point 3 f h hm
    exact no_group _ true [2,3,4,5] Certificates.C3G2345.unsat g hg hgm
      (chain_checked 3) (fun _ => no_three g hg) hp
  · obtain ⟨g,hg,hgm,hp⟩ := normalize_point 4 f h hm
    exact no_group _ true [2,3,4,5,6] Certificates.C4G23456.unsat g hg hgm
      (chain_checked 4) (fun _ => no_three g hg) hp
  · obtain ⟨g,hg,hgm,hp⟩ := normalize_point 5 f h hm
    have hcover : ∀ z : Fin 12, z ∈ allowed 5 →
        z ∈ [2,3,4] ∨ z ∈ [5,6,7] ∨ z ∈ [8,9,10,11] := by decide +kernel
    rcases hcover (g 1 0) hp with hp | hp | hp
    · exact no_group _ true [2,3,4] Certificates.C5G234.unsat g hg hgm
        (chain_checked 5) (fun _ => no_three g hg) hp
    · exact no_group _ true [5,6,7] Certificates.C5G567.unsat g hg hgm
        (chain_checked 5) (fun _ => no_three g hg) hp
    · exact no_group _ true [8,9,10,11] Certificates.C5G891011.unsat g hg hgm
        (chain_checked 5) (fun _ => no_three g hg) hp

private theorem no_operation (f : Fin 12 → Fin 12 → Fin 12) (h : Holds .e1076 f) : False := by
  obtain ⟨g,hg,_,hc⟩ := normalized f h
  obtain ⟨i,hm⟩ := exists_row Certificates.Coverage.unsat g hg hc
  exact transfer_row i (all_rows (target i)) g hg hm

end Spectrum.E1076.OrderTwelve
namespace Spectrum

theorem not_order_1076_12 : ¬ Law1076.HasModel 12 := by
  rintro ⟨M,hM⟩
  exact E1076.OrderTwelve.no_operation M.op ((SmallOrders.holds_iff .e1076 M).mpr hM)

spectrum_assert not_order_1076_12 complete
end Spectrum
