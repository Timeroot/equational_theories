import equational_theories.Definability.ProjectionKernelCounting
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by translations, a projection, and kernel maps. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionKernel3By5Scalars1234
abbrev A := ZMod 3
abbrev B := ZMod 5
abbrev K := Fin 5
def scalarData : Array B := #[1, 2, 3, 4]
def maps (i : Fin 4) : B →+ B where
  toFun x := scalarData[i.val]! * x
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]
def valueData : Array (Array B) := #[#[0, 0, 0, 0, 0], #[0, 1, 2, 3, 4], #[0, 2, 4, 1, 3], #[0, 3, 1, 4, 2], #[0, 4, 3, 2, 1]]
def values (k : K) (x : B) : B :=
  (valueData.getD k.val #[]).getD x.val 0

theorem value_injective : Function.Injective values := by native_decide
theorem value_zero : ∀ k, values k 0 = 0 := by native_decide
theorem value_maps : ∀ k i x, maps i (values k x) = values k (maps i x) := by native_decide
theorem value_coverage : ∀ f : B → B, f 0 = 0 →
    (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f := by native_decide

abbrev Params := Magma.ProjectionKernelFamily.Params A K
@[implicit_reducible] def model (p : Params) : Magma (A × B) :=
  Magma.ProjectionKernelFamily.fam values p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps p (.inl a)

private def law58 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count58 : Fintype.card {p : Params // ZeroTest (model p) law58} = 80 := by native_decide

private def law1437 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count1437 : Fintype.card {p : Params // ZeroTest (model p) law1437} = 80 := by native_decide

private def law3258 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count3258 : Fintype.card {p : Params // ZeroTest (model p) law3258} = 62 := by native_decide

private def law3464 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count3464 : Fintype.card {p : Params // ZeroTest (model p) law3464} = 62 := by native_decide

end Magma.ProjectionKernel3By5Scalars1234

open Magma.ProjectionKernel3By5Scalars1234

theorem Equation3464_not_termStructuralFromFin_Equation58_projectionKernel3By5Scalars1234 : ¬ Law3464.TermStructuralFromFin Law58 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law58) (fun p => ZeroTest (model p) law3464)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count58, count3464]
    decide

/-- info: 'Equation3464_not_termStructuralFromFin_Equation58_projectionKernel3By5Scalars1234' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count3464._native.native_decide.ax_1_1,
 count58._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3464_not_termStructuralFromFin_Equation58_projectionKernel3By5Scalars1234

theorem Equation3464_not_termStructuralFromFin_Equation1437_projectionKernel3By5Scalars1234 : ¬ Law3464.TermStructuralFromFin Law1437 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law1437) (fun p => ZeroTest (model p) law3464)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1437, count3464]
    decide

/-- info: 'Equation3464_not_termStructuralFromFin_Equation1437_projectionKernel3By5Scalars1234' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count1437._native.native_decide.ax_1_1,
 count3464._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3464_not_termStructuralFromFin_Equation1437_projectionKernel3By5Scalars1234

theorem Equation3258_not_termStructuralFromFin_Equation58_projectionKernel3By5Scalars1234 : ¬ Law3258.TermStructuralFromFin Law58 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law58) (fun p => ZeroTest (model p) law3258)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count58, count3258]
    decide

/-- info: 'Equation3258_not_termStructuralFromFin_Equation58_projectionKernel3By5Scalars1234' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count3258._native.native_decide.ax_1_1,
 count58._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3258_not_termStructuralFromFin_Equation58_projectionKernel3By5Scalars1234

theorem Equation3258_not_termStructuralFromFin_Equation1437_projectionKernel3By5Scalars1234 : ¬ Law3258.TermStructuralFromFin Law1437 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law1437) (fun p => ZeroTest (model p) law3258)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1437, count3258]
    decide

/-- info: 'Equation3258_not_termStructuralFromFin_Equation1437_projectionKernel3By5Scalars1234' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count1437._native.native_decide.ax_1_1,
 count3258._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3258_not_termStructuralFromFin_Equation1437_projectionKernel3By5Scalars1234

