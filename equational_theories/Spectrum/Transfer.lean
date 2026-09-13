import equational_theories.Spectrum.Definability
import equational_theories.Definability.PositiveTermsFin
import equational_theories.Definability.PositiveTerms
import equational_theories.Definability.Parastrophic
import equational_theories.Definability.PositiveStructural
import equational_theories.Spectrum.Generated.ImplicationTransfer

/-!
Spectrum equalities obtained from existing definability constructions. These use
only the finite relations when that is all that is available. In particular they
transport every future lower bound and exclusion without reproving any models.
-/

open Law Law.MagmaLaw

namespace Spectrum

theorem spectrum_63_eq_73 : Law63.spectrum = Law73.spectrum :=
  Set.Subset.antisymm
    (subspectral_of_termDefinableFin Equation73_termDefinableFromFin_Equation63)
    (subspectral_of_termDefinableFin Equation63_termDefinableFromFin_Equation73)

theorem spectrum_73_eq_118 : Law73.spectrum = Law118.spectrum :=
  Set.Subset.antisymm
    (subspectral_of_termDefinableFin Equation118_termDefinableFromFin_Equation73)
    (subspectral_of_termDefinableFin Equation73_termDefinableFromFin_Equation118)

theorem spectrum_546_eq_556 : Law546.spectrum = Law556.spectrum :=
  Set.Subset.antisymm
    (subspectral_of_termStructural Equation556_termStructuralFrom_Equation546_parastrophic)
    (subspectral_of_termStructural Equation546_termStructuralFrom_Equation556_parastrophic)

theorem subspectral_63_125 : Law63.Subspectral Law125 :=
  subspectral_of_termDefinableFin Equation125_termDefinableFromFin_Equation63

theorem subspectral_63_1692 : Law63.Subspectral Law1692 :=
  subspectral_of_termDefinableFin Equation1692_termDefinableFromFin_Equation63

theorem spectrum_63_eq_125 : Law63.spectrum = Law125.spectrum :=
  Set.Subset.antisymm subspectral_63_125
    (ImplicationTransfer.path_125_73.trans
      (subspectral_of_termDefinableFin Equation63_termDefinableFromFin_Equation73))

theorem spectrum_63_eq_1692 : Law63.spectrum = Law1692.spectrum :=
  Set.Subset.antisymm subspectral_63_1692
    ((subspectral_of_termStructural Equation73_termStructuralFrom_Equation1692).trans
      (subspectral_of_termDefinableFin Equation63_termDefinableFromFin_Equation73))

theorem spectrum_115_eq_880 : Law115.spectrum = Law880.spectrum :=
  Set.Subset.antisymm
    (subspectral_of_termDefinableFin Equation880_termDefinableFromFin_Equation115)
    ImplicationTransfer.path_880_115

theorem spectrum_481_eq_1496 : Law481.spectrum = Law1496.spectrum :=
  Set.Subset.antisymm
    (subspectral_of_termDefinableFin Equation1496_termDefinableFromFin_Equation481)
    ImplicationTransfer.path_1496_481

theorem spectrum_883_eq_1323 : Law883.spectrum = Law1323.spectrum :=
  Set.Subset.antisymm
    (subspectral_of_termDefinableFin Equation1323_termDefinableFromFin_Equation883)
    (subspectral_of_termDefinableFin Equation883_termDefinableFromFin_Equation1323)

theorem spectrum_883_eq_1526 : Law883.spectrum = Law1526.spectrum :=
  Set.Subset.antisymm
    (subspectral_of_termDefinableFin Equation1526_termDefinableFromFin_Equation883)
    (subspectral_of_termDefinableFin Equation883_termDefinableFromFin_Equation1526)

theorem spectrum_695_eq_887 : Law695.spectrum = Law887.spectrum :=
  Set.Subset.antisymm
    (subspectral_of_termDefinable Equation887_termDefinableFrom_Equation695)
    ImplicationTransfer.path_887_695

end Spectrum
