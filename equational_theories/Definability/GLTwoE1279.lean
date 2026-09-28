import equational_theories.Definability.GLTwoE63
import Mathlib.Algebra.Field.ZMod

/-! E1279 and E1110 cannot first-order define E63, even on finite carriers.
The witness is the 841-element scalar-linear magma on F29²; only a
29-element scalar polynomial check is performed in the proof. -/

set_option maxHeartbeats 2000000

namespace Definability.GLTwoE1279

instance : Fact (Nat.Prime 29) := ⟨by decide⟩

open GLTwoE63

private abbrev K := ZMod 29

lemma source_law : @Equation1279 (V K) (source 4 11) := by
  intro x y
  apply Prod.ext
  · change x.1 = 4*y.1+11*(4*(4*(4*x.1+11*x.1)+11*y.1)+11*y.1)
    ring_nf
    rw [show (2640:K) = 1 by decide, show (609:K) = 0 by decide]
    simp
  · change x.2 = 4*y.2+11*(4*(4*(4*x.2+11*x.2)+11*y.2)+11*y.2)
    ring_nf
    rw [show (2640:K) = 1 by decide, show (609:K) = 0 by decide]
    simp

lemma no_root : ∀ d : K, d^5+d^4+1 ≠ 0 := by
  decide

lemma source_law1110 : @Equation1110 (V K) (source 6 28) := by
  intro x y
  apply Prod.ext
  · change x.1 = 6*y.1+28*(6*(6*y.1+28*(6*x.1+28*x.1))+28*y.1)
    ring_nf
    rw [show (1798:K) = 0 by decide, show (159936:K) = 1 by decide]
    simp
  · change x.2 = 6*y.2+28*(6*(6*y.2+28*(6*x.2+28*x.2))+28*y.2)
    ring_nf
    rw [show (1798:K) = 0 by decide, show (159936:K) = 1 by decide]
    simp

end Definability.GLTwoE1279

open Law Law.MagmaLaw Definability.GLTwoE63 Definability.GLTwoE1279

theorem Equation63_not_definableFromFin_Equation1279_glTwo :
    ¬ Law63.DefinableFromFin Law1279 :=
  not_definableFromFin (4 : ZMod 29) 11
    ((@Law1279.models_iff _ (source 4 11)).mpr source_law) (by decide) no_root

/-- info: 'Equation63_not_definableFromFin_Equation1279_glTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation63_not_definableFromFin_Equation1279_glTwo


theorem Equation63_not_definableFromFin_Equation1110_glTwo :
    ¬ Law63.DefinableFromFin Law1110 :=
  not_definableFromFin (6 : ZMod 29) 28
    ((@Law1110.models_iff _ (source 6 28)).mpr source_law1110) (by decide) no_root

/-- info: 'Equation63_not_definableFromFin_Equation1110_glTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation63_not_definableFromFin_Equation1110_glTwo
