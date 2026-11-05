import equational_theories.Parastrophes.TranslationChains

/-!
# The other image question across a known parastrophic correspondence

If L's left divisions are exactly K, and L always admits left division,
then the right-division images of L and K differ just by opposite.
Consequently their right-image single-equation questions are equivalent.
The dual statement holds after exchanging left and right.

These are dependencies between questions, not unconditional positive or
negative answers to those questions. In particular, E464 and E511 have
equivalent finite right-image questions; solving either solves both.
No full quasigroup assumption is needed: only the side used in the known
correspondence must be present throughout the source class.
-/
namespace Parastrophes
open Law

theorem inImage_right_of_left_characterizes {scope L K}
    (h : Characterizes scope L .left K)
    (hs : SideQuasigroupLaw scope L .left)
    {G : Type} (R : Magma G) (hG : scope.Allows G) :
    InImage L .right R ↔ InImage K .right (opposite R) := by
  constructor
  · rintro ⟨M, hm, hr⟩
    obtain ⟨D, hd, hl⟩ := (characterizes_symm h hs G M hG).mp hm
    exact ⟨D, hd, right_after_left (division_symm hl) hr⟩
  · rintro ⟨D, hd, hr⟩
    obtain ⟨M, hm, hl⟩ := (h G D hG).mp hd
    refine ⟨M, hm, ?_⟩
    simpa only [opposite_opposite] using right_after_left (division_symm hl) hr

theorem inImage_left_of_right_characterizes {scope L K}
    (h : Characterizes scope L .right K)
    (hs : SideQuasigroupLaw scope L .right)
    {G : Type} (D : Magma G) (hG : scope.Allows G) :
    InImage L .left D ↔ InImage K .left (opposite D) := by
  constructor
  · rintro ⟨M, hm, hl⟩
    obtain ⟨R, hr, hd⟩ := (characterizes_symm h hs G M hG).mp hm
    exact ⟨R, hr, left_after_right hl (division_symm hd)⟩
  · rintro ⟨R, hr, hl⟩
    obtain ⟨M, hm, hd⟩ := (h G R hG).mp hr
    refine ⟨M, hm, ?_⟩
    simpa only [opposite_opposite] using left_after_right hl (division_symm hd)

/-- Compose exact image descriptions, dualizing the final target. -/
theorem characterizes_right_after_left {scope L K T}
    (h : Characterizes scope L .left K)
    (hs : SideQuasigroupLaw scope L .left)
    (ht : Characterizes scope K .right T) :
    Characterizes scope L .right T.dual := by
  intro G D hG
  exact (satisfies_opposite (opposite D) T).trans
    ((ht G (opposite D) hG).trans
      (inImage_right_of_left_characterizes h hs D hG).symm)

theorem characterizes_left_after_right {scope L K T}
    (h : Characterizes scope L .right K)
    (hs : SideQuasigroupLaw scope L .right)
    (ht : Characterizes scope K .left T) :
    Characterizes scope L .left T.dual := by
  intro G D hG
  exact (satisfies_opposite (opposite D) T).trans
    ((ht G (opposite D) hG).trans
      (inImage_left_of_right_characterizes h hs D hG).symm)

/-- This transfers negative answers as well as positive answers. It does
not require that either unknown image is already represented in the catalogue. -/
theorem singleEquation_right_iff_of_left {scope L K}
    (h : Characterizes scope L .left K)
    (hs : SideQuasigroupLaw scope L .left) :
    SingleEquation scope L .right ↔ SingleEquation scope K .right := by
  constructor
  · rintro ⟨T, ht⟩
    exact ⟨T.dual, characterizes_right_after_left (characterizes_symm h hs)
      (characterizes_sideQuasigroup h) ht⟩
  · rintro ⟨T, ht⟩
    exact ⟨T.dual, characterizes_right_after_left h hs ht⟩

theorem singleEquation_left_iff_of_right {scope L K}
    (h : Characterizes scope L .right K)
    (hs : SideQuasigroupLaw scope L .right) :
    SingleEquation scope L .left ↔ SingleEquation scope K .left := by
  constructor
  · rintro ⟨T, ht⟩
    exact ⟨T.dual, characterizes_left_after_right (characterizes_symm h hs)
      (characterizes_sideQuasigroup h) ht⟩
  · rintro ⟨T, ht⟩
    exact ⟨T.dual, characterizes_left_after_right h hs ht⟩

/-- These two open finite fields are one independent research problem. -/
theorem right464_iff_right511_fin :
    SingleEquation .fin Law464 .right ↔ SingleEquation .fin Law511 .right :=
  singleEquation_right_iff_of_left Catalogue.left_characterizes464_fin_chain
    (quasigroup_side Catalogue.quasigroup464_fin .left)

end Parastrophes
