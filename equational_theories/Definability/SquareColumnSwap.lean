import equational_theories.Definability.SquareSwap

/-! Swapping the two squares exchanges row and column constraints on the
square image or the full product image. Recovery uses the same involution. -/
open Law Law.MagmaLaw
namespace SquareColumnSwap
variable {G : Type} (M : Magma G)

theorem on_squares (h : @Equation310 G M) (a b : G) :
    (QFOp.squareSwap.magma M).op a (M.op b b) = M.op (M.op b b) (M.op b b) := by
  classical
  rw [QFOp.squareSwap_apply, ← h a b]
  simp

theorem target4272 (h : @Equation310 G M) :
    @Equation4272 G (QFOp.squareSwap.magma M) := by
  intro a b
  rw [QFOp.squareSwap_square, on_squares M h, on_squares M h]

theorem on_products (h : @Equation311 G M) (a b c : G) :
    (QFOp.squareSwap.magma M).op a (M.op b c) = M.op (M.op b c) (M.op b c) := by
  classical
  rw [QFOp.squareSwap_apply, ← h a b c]
  simp

theorem target4300 (h : @Equation311 G M) :
    @Equation4300 G (QFOp.squareSwap.magma M) := by
  intro a b c
  obtain ⟨u,v,huv⟩ := SquareSwap.E3503.image M a b
  rw [huv, on_products M h, on_products M h]

end SquareColumnSwap

theorem Equation4272_structuralFrom_Equation310_squareColumns :
    Law4272.StructuralFrom Law310 :=
  structuralFrom_squareSwap fun {G} M hM =>
    (@Law4272.models_iff G (QFOp.squareSwap.magma M)).mpr
      (SquareColumnSwap.target4272 M ((@Law310.models_iff G M).mp hM))

theorem Equation4300_structuralFrom_Equation311_squareColumns :
    Law4300.StructuralFrom Law311 :=
  structuralFrom_squareSwap fun {G} M hM =>
    (@Law4300.models_iff G (QFOp.squareSwap.magma M)).mpr
      (SquareColumnSwap.target4300 M ((@Law311.models_iff G M).mp hM))

/-- info: 'Equation4272_structuralFrom_Equation310_squareColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4272_structuralFrom_Equation310_squareColumns
/-- info: 'Equation4300_structuralFrom_Equation311_squareColumns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4300_structuralFrom_Equation311_squareColumns
