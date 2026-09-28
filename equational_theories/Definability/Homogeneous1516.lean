import equational_theories.Definability.Homogeneous1516.Classification
import equational_theories.Definability.Homogeneous1516.Sources

/-! Finite FO-definability obstructions on 841-element scalar magmas.
Every definable E1516 companion would be GL(2,29)-equivariant; its restriction
to a line is idempotent by the checked homogeneous classification. The E63
root obstruction then rules it out. The four explicit LRAT certificate
checks use the repository's declared native-computation trust boundary. -/
open Law Law.MagmaLaw Definability.Homogeneous1516 Definability.GLTwoE63
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

theorem Equation1516_not_definableFromFin_Equation467 :
    ¬ Law1516.DefinableFromFin Law467 :=
  Definability.GLTwo1516.not_definableFromFin (8 : ZMod 29) 12
    ((@Law467.models_iff _ (source 8 12)).mpr source467)
    (by decide) no_root classification

theorem Equation1516_not_definableFromFin_Equation704 :
    ¬ Law1516.DefinableFromFin Law704 :=
  Definability.GLTwo1516.not_definableFromFin (21 : ZMod 29) 27
    ((@Law704.models_iff _ (source 21 27)).mpr source704)
    (by decide) no_root classification

theorem Equation1516_not_definableFromFin_Equation1279 :
    ¬ Law1516.DefinableFromFin Law1279 :=
  Definability.GLTwo1516.not_definableFromFin (4 : ZMod 29) 11
    ((@Law1279.models_iff _ (source 4 11)).mpr source1279)
    (by decide) no_root classification

/-- A second proof of the already known E1110 obstruction, by the same construction. -/
theorem Equation1516_not_definableFromFin_Equation1110_homogeneous :
    ¬ Law1516.DefinableFromFin Law1110 :=
  Definability.GLTwo1516.not_definableFromFin (6 : ZMod 29) 28
    ((@Law1110.models_iff _ (source 6 28)).mpr source1110)
    (by decide) no_root classification

theorem Equation1516_not_definableFrom_Equation467 :
    ¬ Law1516.DefinableFrom Law467 :=
  fun h => Equation1516_not_definableFromFin_Equation467 (definableFin_of_definable h)

theorem Equation1516_not_definableFrom_Equation704 :
    ¬ Law1516.DefinableFrom Law704 :=
  fun h => Equation1516_not_definableFromFin_Equation704 (definableFin_of_definable h)

theorem Equation1516_not_definableFrom_Equation1279 :
    ¬ Law1516.DefinableFrom Law1279 :=
  fun h => Equation1516_not_definableFromFin_Equation1279 (definableFin_of_definable h)

spectrum_assert Equation1516_not_definableFromFin_Equation467 complete
spectrum_assert Equation1516_not_definableFromFin_Equation704 complete
spectrum_assert Equation1516_not_definableFromFin_Equation1279 complete
spectrum_assert Equation1516_not_definableFromFin_Equation1110_homogeneous complete
spectrum_assert Equation1516_not_definableFrom_Equation467 complete
spectrum_assert Equation1516_not_definableFrom_Equation704 complete
spectrum_assert Equation1516_not_definableFrom_Equation1279 complete
