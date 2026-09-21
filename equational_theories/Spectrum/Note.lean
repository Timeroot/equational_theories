import equational_theories.Spectrum.NotePending
import equational_theories.Spectrum.Exact
import equational_theories.Spectrum.Transfer
import equational_theories.Spectrum.CentralCardinality
import equational_theories.Spectrum.WeakCentralSpectrum

/-!
Exact formulas stated in §3 of the note, with proved supplements. **Some proofs depend on the explicit
obligations in `NotePending`**: these distinguish available proofs awaiting Lean
from elided arguments not yet reconstructed. Use `#spectrum_status` to inspect
a declaration's actual dependencies, or consult `Catalogue.lean`.
Question-marked formulas require independent proofs (as now provided for E1485).
Unknown cases receive bounds in
`Generated.NoteBounds`, and all 4694 laws are covered by `Catalogue`.
-/

open Law Law.MagmaLaw
namespace Spectrum.Note

theorem exact_2 : Law2.spectrum = ({1} : Set ℕ) := spectrum_two

theorem exact_66 : Law66.spectrum = residues 3 {0, 1} {6} :=
  Set.Subset.antisymm (fun _ h => Pending.orders_66 h)
    (fun _ h => ⟨h.1, Pending.models_66 h⟩)

theorem exact_167 : Law167.spectrum = residues 4 {0, 1} ∅ :=
  Set.Subset.antisymm (fun _ h => Pending.orders_167 h)
    (fun _ h => ⟨h.1, Pending.models_167 h⟩)

theorem exact_168 : Law168.spectrum = squares := by
  apply Set.Subset.antisymm (fun _ h => orders_168 h)
  rintro n ⟨hn, k, rfl⟩
  exact ⟨hn, square_168 k⟩

theorem exact_474 : Law474.spectrum = positiveExcept {2, 4} := by
  simpa [positiveExcept] using spectrum_474

theorem exact_546 : Law546.spectrum = sumTwoSquares :=
  Set.Subset.antisymm (fun _ h => Pending.orders_546 h)
    (fun _ h => ⟨h.1, Pending.models_546 h⟩)

theorem exact_556 : Law556.spectrum = sumTwoSquares :=
  spectrum_546_eq_556.symm.trans exact_546

theorem exact_887 : Law887.spectrum = residues 3 {1, 2} {7} :=
  Set.Subset.antisymm (fun _ h => Pending.orders_887 h)
    (fun _ h => ⟨h.1, Pending.models_887 h⟩)

theorem exact_695 : Law695.spectrum = residues 3 {1, 2} {7} :=
  spectrum_695_eq_887.trans exact_887

theorem exact_895 : Law895.spectrum = powersTwo := by
  apply Set.Subset.antisymm (fun _ h => Pending.orders_895 h)
  rintro n ⟨k, rfl⟩
  exact ⟨by positivity, power_two_895 k⟩

theorem exact_898 : Law898.spectrum = powersTwo := by
  apply Set.Subset.antisymm (fun _ h => Pending.orders_898 h)
  rintro n ⟨k, rfl⟩
  exact ⟨by positivity, power_two_898 k⟩

/-- The E1485 conjecture in the note, now proved by exact degree halving. -/
theorem exact_1485 : Law1485.spectrum = squares ∪ twiceSquares := spectrum_1485

theorem exact_1685 : Law1685.spectrum = positiveExcept {2} := by
  simpa [positiveExcept] using spectrum_1685

end Spectrum.Note
