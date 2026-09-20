import equational_theories.Definability.ProjectionKernelCounting
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by translations, a projection, and kernel maps. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionKernel2By8Scalars1357
abbrev A := ZMod 2
abbrev B := ZMod 8
abbrev K := Fin 64
def scalarData : Array B := #[1, 3, 5, 7]
def maps (i : Fin 4) : B →+ B where
  toFun x := scalarData[i.val]! * x
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]
def valueData : Array (Array B) := #[#[0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 0, 0, 4, 0, 0, 0], #[0, 0, 2, 0, 0, 0, 6, 0], #[0, 0, 2, 0, 4, 0, 6, 0], #[0, 0, 4, 0, 0, 0, 4, 0], #[0, 0, 4, 0, 4, 0, 4, 0], #[0, 0, 6, 0, 0, 0, 2, 0], #[0, 0, 6, 0, 4, 0, 2, 0], #[0, 1, 0, 3, 0, 5, 0, 7], #[0, 1, 0, 3, 4, 5, 0, 7], #[0, 1, 2, 3, 0, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 4, 3, 0, 5, 4, 7], #[0, 1, 4, 3, 4, 5, 4, 7], #[0, 1, 6, 3, 0, 5, 2, 7], #[0, 1, 6, 3, 4, 5, 2, 7], #[0, 2, 0, 6, 0, 2, 0, 6], #[0, 2, 0, 6, 4, 2, 0, 6], #[0, 2, 2, 6, 0, 2, 6, 6], #[0, 2, 2, 6, 4, 2, 6, 6], #[0, 2, 4, 6, 0, 2, 4, 6], #[0, 2, 4, 6, 4, 2, 4, 6], #[0, 2, 6, 6, 0, 2, 2, 6], #[0, 2, 6, 6, 4, 2, 2, 6], #[0, 3, 0, 1, 0, 7, 0, 5], #[0, 3, 0, 1, 4, 7, 0, 5], #[0, 3, 2, 1, 0, 7, 6, 5], #[0, 3, 2, 1, 4, 7, 6, 5], #[0, 3, 4, 1, 0, 7, 4, 5], #[0, 3, 4, 1, 4, 7, 4, 5], #[0, 3, 6, 1, 0, 7, 2, 5], #[0, 3, 6, 1, 4, 7, 2, 5], #[0, 4, 0, 4, 0, 4, 0, 4], #[0, 4, 0, 4, 4, 4, 0, 4], #[0, 4, 2, 4, 0, 4, 6, 4], #[0, 4, 2, 4, 4, 4, 6, 4], #[0, 4, 4, 4, 0, 4, 4, 4], #[0, 4, 4, 4, 4, 4, 4, 4], #[0, 4, 6, 4, 0, 4, 2, 4], #[0, 4, 6, 4, 4, 4, 2, 4], #[0, 5, 0, 7, 0, 1, 0, 3], #[0, 5, 0, 7, 4, 1, 0, 3], #[0, 5, 2, 7, 0, 1, 6, 3], #[0, 5, 2, 7, 4, 1, 6, 3], #[0, 5, 4, 7, 0, 1, 4, 3], #[0, 5, 4, 7, 4, 1, 4, 3], #[0, 5, 6, 7, 0, 1, 2, 3], #[0, 5, 6, 7, 4, 1, 2, 3], #[0, 6, 0, 2, 0, 6, 0, 2], #[0, 6, 0, 2, 4, 6, 0, 2], #[0, 6, 2, 2, 0, 6, 6, 2], #[0, 6, 2, 2, 4, 6, 6, 2], #[0, 6, 4, 2, 0, 6, 4, 2], #[0, 6, 4, 2, 4, 6, 4, 2], #[0, 6, 6, 2, 0, 6, 2, 2], #[0, 6, 6, 2, 4, 6, 2, 2], #[0, 7, 0, 5, 0, 3, 0, 1], #[0, 7, 0, 5, 4, 3, 0, 1], #[0, 7, 2, 5, 0, 3, 6, 1], #[0, 7, 2, 5, 4, 3, 6, 1], #[0, 7, 4, 5, 0, 3, 4, 1], #[0, 7, 4, 5, 4, 3, 4, 1], #[0, 7, 6, 5, 0, 3, 2, 1], #[0, 7, 6, 5, 4, 3, 2, 1]]
def values (k : K) (x : B) : B :=
  (valueData.getD k.val #[]).getD x.val 0

theorem value_injective : Function.Injective values := by native_decide
theorem value_zero : ∀ k, values k 0 = 0 := by native_decide
theorem value_maps : ∀ k i x, maps i (values k x) = values k (maps i x) := by native_decide
def representativeData : Array B := #[0, 1, 2, 4]
def representative (i : Fin 4) : B := representativeData.getD i.val 0
def transportData : Array (Fin 4 × Fin 4) := #[(0, 3), (1, 0), (2, 2), (1, 1), (3, 3), (1, 2), (2, 3), (1, 3)]
def transport (b : B) := transportData.getD b.val (0, 0)
def choiceData : Array (Array B) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 2, 4, 6], #[0, 4]]
def sizes (i : Fin 4) : ℕ := (choiceData.getD i.val #[]).size
def choices (i : Fin 4) (q : Fin (sizes i)) : B := (choiceData.getD i.val #[]).getD q.val 0
def stabilizerData : Array (Array (Fin 4)) := #[#[0, 1, 2, 3], #[0, 0, 0, 0], #[0, 2, 0, 0], #[0, 1, 2, 3]]
def stabilizers (i : Fin 4) (j : Fin 4) := (stabilizerData.getD i.val #[]).getD j.val 0
theorem chart_transport : ∀ b, maps (transport b).2 (representative (transport b).1) = b := by native_decide
theorem chart_fixed : ∀ i j, maps (stabilizers i j) (representative i) = representative i := by native_decide
theorem chart_choices : ∀ i b, (representative i = 0 → b = 0) →
    (∀ j, maps (stabilizers i j) b = b) → ∃ q, choices i q = b := by native_decide
theorem chart_covered : ∀ p : (i : Fin 4) → Fin (sizes i), ∃ k, ∀ b,
    values k b = maps (transport b).2 (choices (transport b).1 (p (transport b).1)) := by native_decide
theorem value_coverage : ∀ f : B → B, f 0 = 0 →
    (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f :=
  Magma.ProjectionKernelFamily.kernel_coverage_of_chart maps values representative transport
    sizes choices stabilizers chart_transport chart_fixed chart_choices chart_covered

abbrev Params := Magma.ProjectionKernelFamily.Params A K
@[implicit_reducible] def model (p : Params) : Magma (A × B) :=
  Magma.ProjectionKernelFamily.fam values p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps p (.inl a)

private def law1370 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Fork (.Leaf 2) (.Leaf 1)) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count1370 : Fintype.card {p : Params // ZeroTest (model p) law1370} = 128 := by native_decide

private def law3518 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 0)) (.Leaf 0)))⟩
private theorem count3518 : Fintype.card {p : Params // ZeroTest (model p) law3518} = 96 := by native_decide

end Magma.ProjectionKernel2By8Scalars1357

open Magma.ProjectionKernel2By8Scalars1357

theorem Equation3518_not_termStructuralFromFin_Equation1370_projectionKernel2By8Scalars1357 : ¬ Law3518.TermStructuralFromFin Law1370 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law1370) (fun p => ZeroTest (model p) law3518)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1370, count3518]
    decide

/-- info: 'Equation3518_not_termStructuralFromFin_Equation1370_projectionKernel2By8Scalars1357' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 chart_choices._native.native_decide.ax_1_1,
 chart_covered._native.native_decide.ax_1_1,
 chart_fixed._native.native_decide.ax_1_1,
 chart_transport._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count1370._native.native_decide.ax_1_1,
 count3518._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3518_not_termStructuralFromFin_Equation1370_projectionKernel2By8Scalars1357

