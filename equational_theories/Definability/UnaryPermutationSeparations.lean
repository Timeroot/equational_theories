import equational_theories.Definability.UnaryPermutationRecovery
import equational_theories.Definability.UnaryRayCompanions
import equational_theories.Generated.VampireProven.Proofs1

/-! Infinite square-map obstructions separate E1096 from E1133 and E1167.
The finite variants are already equivalent, so these negatives are unrestricted only. -/

open Law Law.MagmaLaw
namespace UnaryPermutationRecovery

theorem not_1096 {G : Type} (N : Magma G)
    (hbad : ¬ Function.Bijective (fun x => N.op x x)) :
    ¬ Law1096.TermStructuralOnMagma N := by
  rintro ⟨M, hM, hf, hb⟩
  apply not_termStructuralOnMagma N hbad
  exact ⟨M, (@Law1202.models_iff G M).mpr
    (@Equation1096_implies_Equation1202 G M ((@Law1096.models_iff G M).mp hM)), hf, hb⟩

end UnaryPermutationRecovery

theorem Equation1096_not_termStructuralFrom_Equation1167_unaryPermutation :
    ¬ Law1096.TermStructuralFrom Law1167 := by
  intro h
  exact UnaryPermutationRecovery.not_1096 UnaryPermutationRecovery.ray
    (fun hb => UnaryPermutationRecovery.ray_not_surjective_square hb.2)
    (h UnaryPermutationRecovery.ray
      ((@Law1167.models_iff ℕ UnaryPermutationRecovery.ray).mpr
        UnaryPermutationRecovery.ray_law))

theorem Equation1096_not_termStructuralFrom_Equation1133_unaryPermutation :
    ¬ Law1096.TermStructuralFrom Law1133 := by
  intro h
  exact UnaryPermutationRecovery.not_1096 UnaryPermutationRecovery.predecessorRay
    (fun hb => UnaryPermutationRecovery.predecessorRay_not_injective_square hb.1)
    (h UnaryPermutationRecovery.predecessorRay
      ((@Law1133.models_iff ℕ UnaryPermutationRecovery.predecessorRay).mpr
        UnaryPermutationRecovery.predecessorRay_law))

/-- info: 'Equation1096_not_termStructuralFrom_Equation1167_unaryPermutation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1096_not_termStructuralFrom_Equation1167_unaryPermutation
/-- info: 'Equation1096_not_termStructuralFrom_Equation1133_unaryPermutation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1096_not_termStructuralFrom_Equation1133_unaryPermutation
