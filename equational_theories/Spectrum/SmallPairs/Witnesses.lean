import equational_theories.Spectrum.SmallPairs.Basic
import equational_theories.Spectrum.Status
import Mathlib.Data.Fin.VecNotation

/-! Small positive witnesses. Generated from data/spectrum/witnesses.json
by scripts/spectrum_small_pair_certificates.py. Every table is checked
by kernel reduction, with no native computation or admitted proof. -/

namespace Spectrum.SmallPairs

@[implicit_reducible]
def table_1313_9 : Magma (Fin 9) :=
  ⟨fun x y => ![![1, 2, 0, 4, 5, 3, 7, 8, 6],
    ![8, 6, 7, 2, 0, 1, 5, 3, 4],
    ![3, 4, 5, 6, 7, 8, 0, 1, 2],
    ![5, 3, 4, 8, 6, 7, 2, 0, 1],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![7, 8, 6, 1, 2, 0, 4, 5, 3],
    ![6, 7, 8, 0, 1, 2, 3, 4, 5],
    ![4, 5, 3, 7, 8, 6, 1, 2, 0],
    ![2, 0, 1, 5, 3, 4, 8, 6, 7]] x y⟩

theorem model_1313_9 : Law1313.HasModel 9 :=
  ⟨table_1313_9, (@Law1313.models_iff _ table_1313_9).mpr (by decide +kernel)⟩
spectrum_assert model_1313_9 complete

end Spectrum.SmallPairs
