import equational_theories.Equations.All
import Mathlib.Data.Fintype.Basic

/-! An eight-element E1483/E1485 model refutes the proposed rank-descent
retraction G(F(y)) = y, and even injectivity of G ∘ F on the smaller row.
All finite statements are checked by kernel reduction. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace Spectrum.E1483.RetractionCounterexample

private def packed : Nat := 0xb0282a10082427f3cf64621e27f3cf10082467e3deb3a9ea

def operation (x y : Fin 8) : Fin 8 :=
  ⟨(packed >>> ((x.val * 8 + y.val) * 3)) % 8, Nat.mod_lt _ (by decide)⟩

local instance : Magma (Fin 8) := ⟨operation⟩

theorem law1483 : Equation1483 (Fin 8) := by decide +kernel

theorem law1485 : Equation1485 (Fin 8) := by decide +kernel

/-- The path is e=0 → a=7 → b=4, with t=e*b=2. -/
theorem path : operation 0 2 = 7 ∧ operation 7 6 = 4 ∧ operation 0 4 = 2 := by
  decide +kernel

def composite (y : Fin 8) : Fin 8 :=
  operation 2 (operation (operation 7 (operation y 2)) 7)

/-- Distinct elements of row(t) have the same composite image. -/
theorem composite_not_injective :
    ∃ x y : Fin 8, (∃ s, operation 2 s = x) ∧ (∃ s, operation 2 s = y) ∧
      x ≠ y ∧ composite x = composite y := by
  exact ⟨0, 4, ⟨2, by decide +kernel⟩, ⟨0, by decide +kernel⟩,
    by decide +kernel, by decide +kernel⟩

theorem composite_not_identity : composite 0 ≠ 0 := by decide +kernel

/-- info: 'Spectrum.E1483.RetractionCounterexample.law1483' does not depend on any axioms -/
#guard_msgs in
#print axioms law1483

/-- info: 'Spectrum.E1483.RetractionCounterexample.composite_not_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms composite_not_injective

end Spectrum.E1483.RetractionCounterexample
