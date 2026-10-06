import equational_theories.Spectrum.Equation667FixedSquare.Certificates.Batch00
import equational_theories.Spectrum.Equation667FixedSquare.Certificates.Batch01
import equational_theories.Spectrum.Equation667FixedSquare.Certificates.Batch02
import equational_theories.Spectrum.Equation667FixedSquare.Certificates.Batch03
import equational_theories.Spectrum.Equation667FixedSquare.Certificates.Batch04
import equational_theories.Spectrum.Equation667FixedSquare.Certificates.Batch05
import equational_theories.Spectrum.Equation667FixedSquare.Certificates.Batch06
import equational_theories.Spectrum.Equation667FixedSquare.Certificates.Batch07

namespace Spectrum.E667.FixedSquare
theorem all_refuted : ∀ i, (natNormalized (Cases.table i) (normalizeCase i)).Unsat := by
  intro i
  fin_cases i
  · exact Certificates.C000.unsat
  · exact Certificates.C001.unsat
  · exact Certificates.C002.unsat
  · exact Certificates.C003.unsat
  · exact Certificates.C004.unsat
  · exact Certificates.C005.unsat
  · exact Certificates.C006.unsat
  · exact Certificates.C007.unsat
  · exact Certificates.C008.unsat
  · exact Certificates.C009.unsat
  · exact Certificates.C010.unsat
  · exact Certificates.C011.unsat
  · exact Certificates.C012.unsat
  · exact Certificates.C013.unsat
  · exact Certificates.C014.unsat
  · exact Certificates.C015.unsat
  · exact Certificates.C016.unsat
  · exact Certificates.C017.unsat
  · exact Certificates.C018.unsat
  · exact Certificates.C019.unsat
  · exact Certificates.C020.unsat
  · exact Certificates.C021.unsat
  · exact Certificates.C022.unsat
  · exact Certificates.C023.unsat
  · exact Certificates.C024.unsat
  · exact Certificates.C025.unsat
  · exact Certificates.C026.unsat
  · exact Certificates.C027.unsat
  · exact Certificates.C028.unsat
  · exact Certificates.C029.unsat
  · exact Certificates.C030.unsat
  · exact Certificates.C031.unsat
  · exact Certificates.C032.unsat
  · exact Certificates.C033.unsat
  · exact Certificates.C034.unsat
  · exact Certificates.C035.unsat
  · exact Certificates.C036.unsat
  · exact Certificates.C037.unsat
  · exact Certificates.C038.unsat
  · exact Certificates.C039.unsat
  · exact Certificates.C040.unsat
  · exact Certificates.C041.unsat
  · exact Certificates.C042.unsat
  · exact Certificates.C043.unsat
  · exact Certificates.C044.unsat
  · exact Certificates.C045.unsat
  · exact Certificates.C046.unsat
  · exact Certificates.C047.unsat
  · exact Certificates.C048.unsat
  · exact Certificates.C049.unsat
  · exact Certificates.C050.unsat
  · exact Certificates.C051.unsat
  · exact Certificates.C052.unsat
  · exact Certificates.C053.unsat
  · exact Certificates.C054.unsat
  · exact Certificates.C055.unsat
  · exact Certificates.C056.unsat
  · exact Certificates.C057.unsat
  · exact Certificates.C058.unsat
  · exact Certificates.C059.unsat
  · exact Certificates.C060.unsat
  · exact Certificates.C061.unsat
  · exact Certificates.C062.unsat
  · exact Certificates.C063.unsat
  · exact Certificates.C064.unsat
  · exact Certificates.C065.unsat
  · exact Certificates.C066.unsat
  · exact Certificates.C067.unsat
  · exact Certificates.C068.unsat
  · exact Certificates.C069.unsat
  · exact Certificates.C070.unsat
  · exact Certificates.C071.unsat
  · exact Certificates.C072.unsat
  · exact Certificates.C073.unsat
  · exact Certificates.C074.unsat
  · exact Certificates.C075.unsat
  · exact Certificates.C076.unsat

theorem not_injective_square (f : Fin 12 → Fin 12 → Fin 12)
    (h : RightIdentityTwelve.Holds f) : ¬ Function.Injective (fun x => f x x) :=
  no_injective_of_refuted all_refuted f h

spectrum_assert not_injective_square complete
end Spectrum.E667.FixedSquare
