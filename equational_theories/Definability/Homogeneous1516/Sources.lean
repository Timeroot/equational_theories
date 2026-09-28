import equational_theories.Definability.GLTwo1516
import Mathlib.Algebra.Field.ZMod

/-! Scalar sources over the 841-element vector space F₂₉² for the E1516
first-order definability obstruction. Source laws are verified coordinatewise;
the only finite enumeration is the 29-element polynomial root check. -/

namespace Definability.Homogeneous1516
open Definability.GLTwoE63
local instance : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- The scalar operation `8x + 12y` satisfies E467. -/
lemma source467 : @Equation467 (V (ZMod 29)) (source 8 12) := by
  have hm (x y : ZMod 29) : x = 8*y + 12*(8*x + 12*(8*x + 12*(8*y+12*y))) := by
    ring_nf
    rw [show (34568 : ZMod 29) = 0 by decide, show (1248 : ZMod 29) = 1 by decide]
    simp
  intro x y
  exact Prod.ext (hm x.1 y.1) (hm x.2 y.2)

/-- The scalar operation `21x + 27y` satisfies E704. -/
lemma source704 : @Equation704 (V (ZMod 29)) (source 21 27) := by
  have hm (x y : ZMod 29) : x = 21*y+27*(21*y+27*(21*(21*x+27*x)+27*y)) := by
    ring_nf
    rw [show (20271 : ZMod 29) = 0 by decide, show (734832 : ZMod 29) = 1 by decide]
    simp
  intro x y
  exact Prod.ext (hm x.1 y.1) (hm x.2 y.2)

/-- The scalar operation `4x + 11y` satisfies E1279. -/
lemma source1279 : @Equation1279 (V (ZMod 29)) (source 4 11) := by
  have hm (x y : ZMod 29) : x = 4*y+11*(4*(4*(4*x+11*x)+11*y)+11*y) := by
    ring_nf
    rw [show (609 : ZMod 29) = 0 by decide, show (2640 : ZMod 29) = 1 by decide]
    simp
  intro x y
  exact Prod.ext (hm x.1 y.1) (hm x.2 y.2)

/-- The scalar operation `6x + 28y` satisfies E1110. -/
lemma source1110 : @Equation1110 (V (ZMod 29)) (source 6 28) := by
  have hm (x y : ZMod 29) : x = 6*y+28*(6*(6*y+28*(6*x+28*x))+28*y) := by
    ring_nf
    rw [show (1798 : ZMod 29) = 0 by decide, show (159936 : ZMod 29) = 1 by decide]
    simp
  intro x y
  exact Prod.ext (hm x.1 y.1) (hm x.2 y.2)

/-- The E63/E1516 general-linear obstruction polynomial has no root in F₂₉. -/
lemma no_root : ∀ d : ZMod 29, d^5+d^4+1 ≠ 0 := by decide +kernel

/-- info: 'Definability.Homogeneous1516.source467' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source467
/-- info: 'Definability.Homogeneous1516.source704' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source704
/-- info: 'Definability.Homogeneous1516.source1279' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source1279
/-- info: 'Definability.Homogeneous1516.source1110' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms source1110
/-- info: 'Definability.Homogeneous1516.no_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_root

end Definability.Homogeneous1516
