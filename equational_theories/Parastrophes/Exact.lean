import equational_theories.Parastrophes.FiniteQuasigroups
import equational_theories.Definability.PositiveStructural
import equational_theories.Parastrophes.Catalogue
import equational_theories.Parastrophes.DivisionTerms
import equational_theories.Definability.Parastrophic

/-! Exact characterizations need both directions, including the relevant division.
A pair of existential structural arrows alone does not establish this. -/
namespace Parastrophes
open Law FreeMagma

/-- Two actual division terms, each sending its source law to the other, give
an exact characterization of the parastrophic image. -/
theorem characterizes_of_terms {scope L K side t u}
    (ht : UniformTermWitness scope L side t)
    (hu : UniformTermWitness scope K side u)
    (hf : ∀ G M, scope.Allows G → @satisfies _ G M L →
      @satisfies _ G (termMagma M t) K)
    (hb : ∀ G M, scope.Allows G → @satisfies _ G M K →
      @satisfies _ G (termMagma M u) L) : Characterizes scope L side K := by
  intro G D hG
  constructor
  · intro hD
    have hM := hb G D hG hD
    exact ⟨termMagma D u, hM, division_symm (hu G D hG hD)⟩
  · rintro ⟨M, hM, hd⟩
    have he := division_unique hd (ht G M hG hM)
    exact he.symm ▸ hf G M hG hM

/-- When division is multiplication itself, the image has exactly the source law. -/
theorem characterizes_self {scope L side}
    (ht : UniformTermWitness scope L side (Lf 0 ⋆ Lf 1)) :
    Characterizes scope L side L := by
  apply characterizes_of_terms ht ht
  all_goals exact fun _ _ _ h => h

/-- When division swaps the arguments, the exact image law is the dual law. -/
theorem characterizes_opposite {scope L side}
    (ht : UniformTermWitness scope L side (Lf 1 ⋆ Lf 0)) :
    Characterizes scope L side L.dual := by
  intro G D hG
  constructor
  · intro hD
    have hM := (satisfies_opposite (opposite D) L).mp hD
    exact ⟨opposite D, hM, ht G _ hG hM⟩
  · rintro ⟨M, hM, hd⟩
    have he : D = opposite M := division_unique hd (ht G M hG hM)
    rw [he]
    exact (satisfies_opposite M L).mpr hM

namespace Catalogue

/-- Gaussian E546 models have the two explicit division terms already recorded. -/
@[parastrophe_result] theorem quasigroup546 : QuasigroupLaw .all Law546 := by
  intro G M _ h
  exact quasigroup_of_divisions (left_term546 G M trivial h) (right_term546 G M trivial h)

/-- The left division term used by the existing E556-to-E546 construction. -/
@[parastrophe_result] theorem left_term556 :
    UniformTermWitness .all Law556 .left (Lf 0 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h556 := (@Law556.models_iff G M).mp h
  have h775 := Equation556_implies_Equation775 G h556
  have h714 := SimpleRewrites.Equation775_implies_Equation714 G h775
  have h1120 := Equation714_implies_Equation1120 G h714
  exact ⟨fun x y => (h714 y x).symm, fun x y => (h1120 y x).symm⟩

/-- E556 inherits the two explicit division terms of E714. -/
@[parastrophe_result] theorem quasigroup556 : QuasigroupLaw .all Law556 := by
  intro G M _ h
  letI : Magma G := M
  have h556 := (@Law556.models_iff G M).mp h
  have h775 := Equation556_implies_Equation775 G h556
  have h714 := SimpleRewrites.Equation775_implies_Equation714 G h775
  have hh := (@Law714.models_iff G M).mpr h714
  exact quasigroup_of_divisions (left_term714 G M trivial hh) (right_term714 G M trivial hh)

/-- E546 and E556 are exactly left-parastrophic on all carriers. -/
@[parastrophe_result] theorem left_characterizes546 : Characterizes .all Law546 .left Law556 := by
  apply characterizes_of_terms left_term546 left_term556
  · intro G M _ h
    apply (@Law556.models_iff G (termMagma M (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))))).mpr
    exact (@Law.MagmaLaw.aux546_556 G M ((@Law546.models_iff G M).mp h))
  · intro G M _ h
    apply (@Law546.models_iff G (termMagma M (Lf 0 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 0)))).mpr
    exact (@Law.MagmaLaw.aux556_546 G M ((@Law556.models_iff G M).mp h))

/-- The converse exact characterization, with the actual inverse division term. -/
@[parastrophe_result] theorem left_characterizes556 : Characterizes .all Law556 .left Law546 := by
  apply characterizes_of_terms left_term556 left_term546
  · intro G M _ h
    apply (@Law546.models_iff G (termMagma M (Lf 0 ⋆ ((Lf 0 ⋆ Lf 1) ⋆ Lf 0)))).mpr
    exact (@Law.MagmaLaw.aux556_546 G M ((@Law556.models_iff G M).mp h))
  · intro G M _ h
    apply (@Law556.models_iff G (termMagma M (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))))).mpr
    exact (@Law.MagmaLaw.aux546_556 G M ((@Law546.models_iff G M).mp h))

/-- E546 right division is the original operation, so its image is exactly E546. -/
@[parastrophe_result] theorem right_characterizes546 : Characterizes .all Law546 .right Law546 :=
  characterizes_self right_term546

/-- The two division terms of E125 work without a finite-carrier assumption. -/
@[parastrophe_result] theorem quasigroup125 : QuasigroupLaw .all Law125 := by
  intro G M _ h
  exact quasigroup_of_divisions (left_term125 G M trivial h) (right_term125 G M trivial h)

/-- An equivalent left division term, matching the existing E125-to-E63 proof. -/
@[parastrophe_result] theorem left_term125_alternate :
    UniformTermWitness .all Law125 .left ((Lf 0 ⋆ Lf 1) ⋆ Lf 0) := by
  intro G M _ h
  letI : Magma G := M
  have h125 := (@Law125.models_iff G M).mp h
  have h229 := Equation125_implies_Equation229 G h125
  exact ⟨fun x y => (h125 y x).symm, fun x y => (h229 y x).symm⟩

/-- The finite E63/E125 correspondence is specifically left division in both directions. -/
@[parastrophe_result] theorem left_characterizes63_fin : Characterizes .fin Law63 .left Law125 := by
  apply characterizes_of_terms left_term63_fin
    (fun G M _ h => left_term125_alternate G M trivial h)
  · intro G M hG h
    letI : Finite G := hG
    apply (@Law125.models_iff G (termMagma M (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))).mpr
    exact @Law.MagmaLaw.aux63_125 G _ M ((@Law63.models_iff G M).mp h)
  · intro G M _ h
    apply (@Law63.models_iff G (termMagma M ((Lf 0 ⋆ Lf 1) ⋆ Lf 0))).mpr
    exact @Law.MagmaLaw.aux125_63 G M ((@Law125.models_iff G M).mp h)

/-- The reverse finite characterization; E63 itself has extra infinite models. -/
@[parastrophe_result] theorem left_characterizes125_fin : Characterizes .fin Law125 .left Law63 := by
  apply characterizes_of_terms
    (fun G M _ h => left_term125_alternate G M trivial h) left_term63_fin
  · intro G M _ h
    apply (@Law63.models_iff G (termMagma M ((Lf 0 ⋆ Lf 1) ⋆ Lf 0))).mpr
    exact @Law.MagmaLaw.aux125_63 G M ((@Law125.models_iff G M).mp h)
  · intro G M hG h
    letI : Finite G := hG
    apply (@Law125.models_iff G (termMagma M (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)))).mpr
    exact @Law.MagmaLaw.aux63_125 G _ M ((@Law63.models_iff G M).mp h)

end Catalogue
end Parastrophes
