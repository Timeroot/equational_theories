import equational_theories.Definability.ProjectionFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Complete projection-compatible families, with independently reproduced counts. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionGroupCount10
abbrev A := (ZMod 5)
abbrev B := (ZMod 2)
abbrev Params := Magma.ProjectionFamily.Params A B
@[implicit_reducible] def model (p : Params) : Magma (A × B) := Magma.ProjectionFamily.fam p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionFamily.family_generators p (.inl a)

private def law49 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem count49 : Fintype.card {p : Params // ZeroTest (model p) law49} = 2421 := by native_decide

private def law819 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem count819 : Fintype.card {p : Params // ZeroTest (model p) law819} = 2405 := by native_decide

end Magma.ProjectionGroupCount10

open Magma.ProjectionGroupCount10

theorem Equation819_not_termStructuralFromFin_Equation49_projectionGroupCount10 : ¬ Law819.TermStructuralFromFin Law49 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionFamily.gen (A := A) (B := B))
    model Magma.ProjectionFamily.family_injective Magma.ProjectionFamily.coverage
    Magma.ProjectionFamily.family_generators
    (fun p => ZeroTest (model p) law49) (fun p => ZeroTest (model p) law819)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count49, count819]
    decide

/-- info: 'Equation819_not_termStructuralFromFin_Equation49_projectionGroupCount10' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 count49._native.native_decide.ax_1_1,
 count819._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation819_not_termStructuralFromFin_Equation49_projectionGroupCount10

