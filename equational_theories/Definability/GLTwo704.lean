import equational_theories.Definability.GLTwoE63
import equational_theories.Definability.FiniteFlavour
import Mathlib.Algebra.Field.ZMod

/-! E704 has a scalar model on `F₂₉²`, whose general-linear symmetries
obstruct every parameter-free first-order E63 operation on the same set. -/

local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

namespace Definability.GLTwo704

open Definability.GLTwoE63

lemma source_models : @Equation704 (V (ZMod 29)) (source 21 27) := by
  have hm (x y : ZMod 29) :
      x = 21*y+27*(21*y+27*(21*(21*x+27*x)+27*y)) := by
    ring_nf
    rw [show (20271 : ZMod 29) = 0 by decide, show (734832 : ZMod 29) = 1 by decide]
    simp
  intro x y
  exact Prod.ext (hm x.1 y.1) (hm x.2 y.2)

lemma no_root : ¬ ∃ d : ZMod 29, d^5+d^4+1 = 0 := by decide

end Definability.GLTwo704

open Law Law.MagmaLaw

/-- The scalar E704 model on 841 points admits no first-order definable E63 companion. -/
theorem Equation63_not_definableFromFin_Equation704 :
    ¬ Law63.DefinableFromFin Law704 := by
  intro h
  obtain ⟨N, hN, hd⟩ := h (Definability.GLTwoE63.source (21 : ZMod 29) 27)
    ((@Law704.models_iff (Definability.GLTwoE63.V (ZMod 29)) (Definability.GLTwoE63.source 21 27)).mpr Definability.GLTwo704.source_models)
  exact Definability.GLTwo704.no_root
    (Definability.GLTwoE63.root_of_definable 21 27 N (by decide) hd
      ((@Law63.models_iff _ N).mp hN))

/-- info: 'Equation63_not_definableFromFin_Equation704' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Equation63_not_definableFromFin_Equation704
