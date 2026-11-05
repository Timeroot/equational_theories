import equational_theories.Equations.All
import equational_theories.Generated.FiniteImplicationSearch.theorems.Inverses1
import equational_theories.Generated.MagmaEgg.small._000
import equational_theories.Generated.MagmaEgg.small._001
import equational_theories.Generated.MagmaEgg.small._002
import equational_theories.Generated.MagmaEgg.small._003
import equational_theories.Generated.MagmaEgg.small._004
import equational_theories.Generated.MagmaEgg.small._005
import equational_theories.Generated.MagmaEgg.small._006
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zy
import equational_theories.Generated.VampireProven.Proofs1
import equational_theories.Generated.VampireProven.Proofs12
import equational_theories.Generated.VampireProven.Proofs3
import equational_theories.Generated.VampireProven.Proofs6
import equational_theories.Parastrophes.Attributes

/-! Explicit division terms recovered from existing equational implications.
Each wrapper checks both inverse identities. These are facts about the actual
division operation, not merely another term-definable magma. -/
namespace Parastrophes.Catalogue
open Law FreeMagma

/-- E1316: the two inverse identities are E707 and E1316, both already proved. -/
@[parastrophe_result] theorem left_term1316 :
    UniformTermWitness .all Law1316 .left (Lf 0 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h1316 : Equation1316 G := (@Law1316.models_iff G M).mp h
  have h2331 : Equation2331 G := by apply_rules [Equation1316_implies_Equation2331]
  have h707 : Equation707 G := by apply_rules [Equation2331_implies_Equation707]
  exact ⟨fun x y => (h707 y x).symm, fun x y => (h1316 y x).symm⟩

/-- E1492: the two inverse identities are E477 and E1492, both already proved. -/
@[parastrophe_result] theorem left_term1492 :
    UniformTermWitness .all Law1492 .left (Lf 1 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 0))) := by
  intro G M _ h
  letI : Magma G := M
  have h1492 : Equation1492 G := (@Law1492.models_iff G M).mp h
  have h2135 : Equation2135 G := by apply_rules [Equation1492_implies_Equation2135]
  have h477 : Equation477 G := by apply_rules [Equation2135_implies_Equation477]
  exact ⟨fun x y => (h477 y x).symm, fun x y => (h1492 y x).symm⟩

/-- E1113: the two inverse identities are E1113 and E2534, both already proved. -/
@[parastrophe_result] theorem left_term1113_fin :
    UniformTermWitness .fin Law1113 .left ((Lf 0 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ Lf 0) := by
  intro G M hG h
  letI : Magma G := M
  letI : Finite G := hG
  have h1113 : Equation1113 G := (@Law1113.models_iff G M).mp h
  have h2534 : Equation2534 G := by apply_rules [Finite.Equation1113_implies_Equation2534]
  exact ⟨fun x y => (h1113 y x).symm, fun x y => (h2534 y x).symm⟩

/-- E546: the two inverse identities are E513 and E513, both already proved. -/
@[parastrophe_result] theorem left_term546 :
    UniformTermWitness .all Law546 .left (Lf 0 ⋆ (Lf 0 ⋆ (Lf 0 ⋆ Lf 1))) := by
  intro G M _ h
  letI : Magma G := M
  have h546 : Equation546 G := (@Law546.models_iff G M).mp h
  have h1967 : Equation1967 G := by apply_rules [Equation546_implies_Equation1967]
  have h562 : Equation562 G := by apply_rules [Equation1967_implies_Equation562]
  have h513 : Equation513 G := by apply_rules [SimpleRewrites.Equation562_implies_Equation513]
  exact ⟨fun x y => (h513 y x).symm, fun x y => (h513 y x).symm⟩

/-- E546: the two inverse identities are E26 and E26, both already proved. -/
@[parastrophe_result] theorem right_term546 :
    UniformTermWitness .all Law546 .right (Lf 0 ⋆ Lf 1) := by
  intro G M _ h
  letI : Magma G := M
  have h546 : Equation546 G := (@Law546.models_iff G M).mp h
  have h1967 : Equation1967 G := by apply_rules [Equation546_implies_Equation1967]
  have h2586 : Equation2586 G := by apply_rules [Equation1967_implies_Equation2586]
  have h1790 : Equation1790 G := by apply_rules [Equation2586_implies_Equation1790]
  have h26 : Equation26 G := by apply_rules [Equation1790_implies_Equation26]
  exact ⟨fun x y => (h26 x y).symm, fun x y => (h26 x y).symm⟩

/-- E66: the two inverse identities are E66 and E170, both already proved. -/
@[parastrophe_result] theorem left_term66 :
    UniformTermWitness .all Law66 .left (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h66 : Equation66 G := (@Law66.models_iff G M).mp h
  have h170 : Equation170 G := by apply_rules [Equation66_implies_Equation170]
  exact ⟨fun x y => (h66 y x).symm, fun x y => (h170 y x).symm⟩

/-- E714: the two inverse identities are E511 and E714, both already proved. -/
@[parastrophe_result] theorem left_term714 :
    UniformTermWitness .all Law714 .left (Lf 0 ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 0))) := by
  intro G M _ h
  letI : Magma G := M
  have h714 : Equation714 G := (@Law714.models_iff G M).mp h
  have h511 : Equation511 G := by apply_rules [Equation714_implies_Equation511]
  exact ⟨fun x y => (h511 y x).symm, fun x y => (h714 y x).symm⟩

/-- E714: the two inverse identities are E2338 and E511, both already proved. -/
@[parastrophe_result] theorem right_term714 :
    UniformTermWitness .all Law714 .right (Lf 1 ⋆ (Lf 1 ⋆ (Lf 1 ⋆ Lf 0))) := by
  intro G M _ h
  letI : Magma G := M
  have h714 : Equation714 G := (@Law714.models_iff G M).mp h
  have h2338 : Equation2338 G := by apply_rules [Equation714_implies_Equation2338]
  have h511 : Equation511 G := by apply_rules [Equation714_implies_Equation511]
  exact ⟨fun x y => (h2338 x y).symm, fun x y => (h511 x y).symm⟩

/-- E898: the two inverse identities are E883 and E2101, both already proved. -/
@[parastrophe_result] theorem left_term898 :
    UniformTermWitness .all Law898 .left ((Lf 1 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h898 : Equation898 G := (@Law898.models_iff G M).mp h
  have h883 : Equation883 G := by apply_rules [SimpleRewrites.Equation898_implies_Equation883]
  have h2316 : Equation2316 G := by apply_rules [Equation898_implies_Equation2316]
  have h2304 : Equation2304 G := by apply_rules [SimpleRewrites.Equation2316_implies_Equation2304]
  have h2101 : Equation2101 G := by apply_rules [Equation2304_implies_Equation2101]
  exact ⟨fun x y => (h883 y x).symm, fun x y => (h2101 y x).symm⟩

/-- E898: the two inverse identities are E2304 and E883, both already proved. -/
@[parastrophe_result] theorem right_term898 :
    UniformTermWitness .all Law898 .right (Lf 1 ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 1))) := by
  intro G M _ h
  letI : Magma G := M
  have h898 : Equation898 G := (@Law898.models_iff G M).mp h
  have h2316 : Equation2316 G := by apply_rules [Equation898_implies_Equation2316]
  have h2304 : Equation2304 G := by apply_rules [SimpleRewrites.Equation2316_implies_Equation2304]
  have h883 : Equation883 G := by apply_rules [SimpleRewrites.Equation898_implies_Equation883]
  exact ⟨fun x y => (h2304 x y).symm, fun x y => (h883 x y).symm⟩

/-- E1073: the two inverse identities are E1113 and E2534, both already proved. -/
@[parastrophe_result] theorem left_term1073 :
    UniformTermWitness .all Law1073 .left ((Lf 0 ⋆ (Lf 1 ⋆ Lf 0)) ⋆ Lf 0) := by
  intro G M _ h
  letI : Magma G := M
  have h1073 : Equation1073 G := (@Law1073.models_iff G M).mp h
  have h2573 : Equation2573 G := by apply_rules [Equation1073_implies_Equation2573]
  have h1155 : Equation1155 G := by apply_rules [Equation2573_implies_Equation1155]
  have h1113 : Equation1113 G := by apply_rules [SimpleRewrites.Equation1155_implies_Equation1113]
  have h2534 : Equation2534 G := by apply_rules [SimpleRewrites.Equation2573_implies_Equation2534]
  exact ⟨fun x y => (h1113 y x).symm, fun x y => (h2534 y x).symm⟩

/-- E1073: the two inverse identities are E2534 and E1113, both already proved. -/
@[parastrophe_result] theorem right_term1073 :
    UniformTermWitness .all Law1073 .right (Lf 1 ⋆ ((Lf 1 ⋆ Lf 0) ⋆ Lf 1)) := by
  intro G M _ h
  letI : Magma G := M
  have h1073 : Equation1073 G := (@Law1073.models_iff G M).mp h
  have h2573 : Equation2573 G := by apply_rules [Equation1073_implies_Equation2573]
  have h2534 : Equation2534 G := by apply_rules [SimpleRewrites.Equation2573_implies_Equation2534]
  have h1155 : Equation1155 G := by apply_rules [Equation2573_implies_Equation1155]
  have h1113 : Equation1113 G := by apply_rules [SimpleRewrites.Equation1155_implies_Equation1113]
  exact ⟨fun x y => (h2534 x y).symm, fun x y => (h1113 x y).symm⟩

/-- E1695: the two inverse identities are E680 and E1695, both already proved. -/
@[parastrophe_result] theorem left_term1695 :
    UniformTermWitness .all Law1695 .left (Lf 1 ⋆ ((Lf 0 ⋆ Lf 0) ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h1695 : Equation1695 G := (@Law1695.models_iff G M).mp h
  have h1932 : Equation1932 G := by apply_rules [Equation1695_implies_Equation1932]
  have h680 : Equation680 G := by apply_rules [Equation1932_implies_Equation680]
  exact ⟨fun x y => (h680 y x).symm, fun x y => (h1695 y x).symm⟩

/-- E125: the two inverse identities are E73 and E125, both already proved. -/
@[parastrophe_result] theorem left_term125 :
    UniformTermWitness .all Law125 .left (Lf 0 ⋆ (Lf 1 ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h125 : Equation125 G := (@Law125.models_iff G M).mp h
  have h73 : Equation73 G := by apply_rules [Equation125_implies_Equation73]
  exact ⟨fun x y => (h73 y x).symm, fun x y => (h125 y x).symm⟩

/-- E125: the two inverse identities are E229 and E73, both already proved. -/
@[parastrophe_result] theorem right_term125 :
    UniformTermWitness .all Law125 .right (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h125 : Equation125 G := (@Law125.models_iff G M).mp h
  have h229 : Equation229 G := by apply_rules [Equation125_implies_Equation229]
  have h73 : Equation73 G := by apply_rules [Equation125_implies_Equation73]
  exact ⟨fun x y => (h229 x y).symm, fun x y => (h73 x y).symm⟩

/-- E880: the two inverse identities are E219 and E880, both already proved. -/
@[parastrophe_result] theorem right_term880 :
    UniformTermWitness .all Law880 .right (Lf 1 ⋆ (Lf 0 ⋆ Lf 0)) := by
  intro G M _ h
  letI : Magma G := M
  have h880 : Equation880 G := (@Law880.models_iff G M).mp h
  have h219 : Equation219 G := by apply_rules [Equation880_implies_Equation219]
  exact ⟨fun x y => (h219 x y).symm, fun x y => (h880 x y).symm⟩

/-- E883: the two inverse identities are E2304 and E883, both already proved. -/
@[parastrophe_result] theorem right_term883_fin :
    UniformTermWitness .fin Law883 .right (Lf 1 ⋆ (Lf 0 ⋆ (Lf 1 ⋆ Lf 1))) := by
  intro G M hG h
  letI : Magma G := M
  letI : Finite G := hG
  have h883 : Equation883 G := (@Law883.models_iff G M).mp h
  have h2304 : Equation2304 G := by apply_rules [Finite.Equation883_implies_Equation2304]
  exact ⟨fun x y => (h2304 x y).symm, fun x y => (h883 x y).symm⟩

/-- E883: the two inverse identities are E883 and E2101, both already proved. -/
@[parastrophe_result] theorem left_term883_fin :
    UniformTermWitness .fin Law883 .left ((Lf 1 ⋆ Lf 0) ⋆ (Lf 0 ⋆ Lf 0)) := by
  intro G M hG h
  letI : Magma G := M
  letI : Finite G := hG
  have h883 : Equation883 G := (@Law883.models_iff G M).mp h
  have h2304 : Equation2304 G := by apply_rules [Finite.Equation883_implies_Equation2304]
  have h2101 : Equation2101 G := by apply_rules [Equation2304_implies_Equation2101]
  exact ⟨fun x y => (h883 y x).symm, fun x y => (h2101 y x).symm⟩

/-- E917: the two inverse identities are E2541 and E917, both already proved. -/
@[parastrophe_result] theorem right_term917_fin :
    UniformTermWitness .fin Law917 .right (Lf 1 ⋆ ((Lf 1 ⋆ Lf 1) ⋆ Lf 0)) := by
  intro G M hG h
  letI : Magma G := M
  letI : Finite G := hG
  have h917 : Equation917 G := (@Law917.models_iff G M).mp h
  have h2541 : Equation2541 G := by apply_rules [Finite.Equation917_implies_Equation2541]
  exact ⟨fun x y => (h2541 x y).symm, fun x y => (h917 x y).symm⟩

/-- E917: the two inverse identities are E917 and E1729, both already proved. -/
@[parastrophe_result] theorem left_term917_fin :
    UniformTermWitness .fin Law917 .left ((Lf 0 ⋆ Lf 0) ⋆ (Lf 1 ⋆ Lf 0)) := by
  intro G M hG h
  letI : Magma G := M
  letI : Finite G := hG
  have h917 : Equation917 G := (@Law917.models_iff G M).mp h
  have h1729 : Equation1729 G := by apply_rules [Finite.Equation917_implies_Equation1729]
  exact ⟨fun x y => (h917 y x).symm, fun x y => (h1729 y x).symm⟩

/-- E63: the two inverse identities are E63 and E1692, both already proved. -/
@[parastrophe_result] theorem left_term63_fin :
    UniformTermWitness .fin Law63 .left (Lf 1 ⋆ (Lf 1 ⋆ Lf 0)) := by
  intro G M hG h
  letI : Magma G := M
  letI : Finite G := hG
  have h63 : Equation63 G := (@Law63.models_iff G M).mp h
  have h1692 : Equation1692 G := by apply_rules [Finite.Equation63_implies_Equation1692]
  exact ⟨fun x y => (h63 y x).symm, fun x y => (h1692 y x).symm⟩

end Parastrophes.Catalogue
