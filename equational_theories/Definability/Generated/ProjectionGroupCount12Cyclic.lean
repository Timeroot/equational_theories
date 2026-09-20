import equational_theories.Definability.ProjectionFamilyCounting
import Mathlib.Data.ZMod.Basic

/-! Complete projection-compatible families, with independently reproduced counts. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionGroupCount12Cyclic
abbrev A := (ZMod 4)
abbrev B := (ZMod 3)
abbrev Params := Magma.ProjectionFamily.Params A B
@[implicit_reducible] def model (p : Params) : Magma (A × B) := Magma.ProjectionFamily.fam p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionFamily.family_generators p (.inl a)

private def law446 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Fork (.Leaf 0) (.Leaf 0)))))⟩
private theorem count446 : Fintype.card {p : Params // ZeroTest (model p) law446} = 3578 := by native_decide

private def law3264 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count3264 : Fintype.card {p : Params // ZeroTest (model p) law3264} = 2780 := by native_decide

end Magma.ProjectionGroupCount12Cyclic

open Magma.ProjectionGroupCount12Cyclic

theorem Equation3264_not_termStructuralFromFin_Equation446_projectionGroupCount12Cyclic : ¬ Law3264.TermStructuralFromFin Law446 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionFamily.gen (A := A) (B := B))
    model Magma.ProjectionFamily.family_injective Magma.ProjectionFamily.coverage
    Magma.ProjectionFamily.family_generators
    (fun p => ZeroTest (model p) law446) (fun p => ZeroTest (model p) law3264)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count446, count3264]
    decide

/-- info: 'Equation3264_not_termStructuralFromFin_Equation446_projectionGroupCount12Cyclic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 count3264._native.native_decide.ax_1_1,
 count446._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3264_not_termStructuralFromFin_Equation446_projectionGroupCount12Cyclic

