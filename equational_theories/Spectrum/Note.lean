import equational_theories.Spectrum.NotePending
import equational_theories.Spectrum.Exact
import equational_theories.Spectrum.Transfer
import equational_theories.Spectrum.CentralCardinality
import equational_theories.Spectrum.WeakCentralSpectrum
import equational_theories.Spectrum.SmallCertificates
import equational_theories.Spectrum.Equation1719
import equational_theories.Spectrum.Equation1489
import equational_theories.Spectrum.Equation1480
import equational_theories.Spectrum.QuasigroupSpectra

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

theorem exact_115 : Law115.spectrum = positiveExcept {2, 6} := spectrum_115

theorem exact_873 : Law873.spectrum = positiveExcept {2, 6} := spectrum_873

theorem exact_880 : Law880.spectrum = positiveExcept {2, 6} :=
  spectrum_115_eq_880.symm.trans exact_115

theorem exact_481 : Law481.spectrum = positiveExcept {3, 6} := spectrum_481

theorem exact_1496 : Law1496.spectrum = positiveExcept {3, 6} :=
  spectrum_481_eq_1496.symm.trans exact_481

theorem exact_1719 : Law1719.spectrum = positiveExcept {2} := spectrum_1719

theorem exact_1489 : Law1489.spectrum = positiveExcept {2,4} := spectrum_1489

theorem exact_1480 : Law1480.spectrum = positiveExcept {2,3} := spectrum_1480

end Spectrum.Note
