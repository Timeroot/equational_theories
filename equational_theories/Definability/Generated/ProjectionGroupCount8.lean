import equational_theories.Definability.ProjectionFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Complete projection-compatible families, with independently reproduced counts. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionGroupCount8
abbrev A := (ZMod 2)
abbrev B := (ZMod 2 × ZMod 2)
abbrev Params := Magma.ProjectionFamily.Params A B
@[implicit_reducible] def model (p : Params) : Magma (A × B) := Magma.ProjectionFamily.fam p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionFamily.family_generators p (.inl a)

private def law117 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count117 : Fintype.card {p : Params // ZeroTest (model p) law117} = 28 := by native_decide

private def law1353 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Fork (.Leaf 2) (.Leaf 0)) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count1353 : Fintype.card {p : Params // ZeroTest (model p) law1353} = 32 := by native_decide

private def law3518 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 0)) (.Leaf 0)))⟩
private theorem count3518 : Fintype.card {p : Params // ZeroTest (model p) law3518} = 28 := by native_decide

end Magma.ProjectionGroupCount8

open Magma.ProjectionGroupCount8

theorem Equation117_not_termStructuralFromFin_Equation1353_projectionGroupCount8 : ¬ Law117.TermStructuralFromFin Law1353 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionFamily.gen (A := A) (B := B))
    model Magma.ProjectionFamily.family_injective Magma.ProjectionFamily.coverage
    Magma.ProjectionFamily.family_generators
    (fun p => ZeroTest (model p) law1353) (fun p => ZeroTest (model p) law117)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1353, count117]
    decide

/-- info: 'Equation117_not_termStructuralFromFin_Equation1353_projectionGroupCount8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 count117._native.native_decide.ax_1_1,
 count1353._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation117_not_termStructuralFromFin_Equation1353_projectionGroupCount8

theorem Equation3518_not_termStructuralFromFin_Equation1353_projectionGroupCount8 : ¬ Law3518.TermStructuralFromFin Law1353 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionFamily.gen (A := A) (B := B))
    model Magma.ProjectionFamily.family_injective Magma.ProjectionFamily.coverage
    Magma.ProjectionFamily.family_generators
    (fun p => ZeroTest (model p) law1353) (fun p => ZeroTest (model p) law3518)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1353, count3518]
    decide

/-- info: 'Equation3518_not_termStructuralFromFin_Equation1353_projectionGroupCount8' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 count1353._native.native_decide.ax_1_1,
 count3518._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3518_not_termStructuralFromFin_Equation1353_projectionGroupCount8

