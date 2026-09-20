import equational_theories.Definability.ProjectionKernelCounting
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by translations, a projection, and kernel maps. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionVector3By8Upper
abbrev A := ZMod 3
abbrev B := (ZMod 2 × ZMod 2 × ZMod 2)
def index (x : B) : ℕ := 1 * x.1.val + 2 * x.2.1.val + 4 * x.2.2.val
abbrev K := Fin 32
def mapData : Array (Array B) := #[#[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 1, 1), (1, 1, 1), (0, 0, 1), (1, 0, 1)], #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (1, 0, 1), (0, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 1, 1), (1, 1, 1), (1, 0, 1), (0, 0, 1)], #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (1, 1, 1), (0, 1, 1), (1, 0, 1), (0, 0, 1)], #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (1, 1, 1), (0, 1, 1), (0, 0, 1), (1, 0, 1)]]
def mapFunction (i : Fin 8) (x : B) : B :=
  (mapData.getD i.val #[]).getD (index x) 0
theorem map_zero : ∀ i, mapFunction i 0 = 0 := by native_decide
theorem map_add : ∀ i x y, mapFunction i (x + y) = mapFunction i x + mapFunction i y := by native_decide
def maps (i : Fin 8) : B →+ B where
  toFun := mapFunction i
  map_zero' := map_zero i
  map_add' := map_add i
def valueData : Array (Array B) := #[#[(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], #[(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0)], #[(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (0, 0, 0), (1, 0, 0), (1, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], #[(0, 0, 0), (0, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0)], #[(0, 0, 0), (0, 0, 0), (1, 0, 0), (1, 0, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (0, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (0, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], #[(0, 0, 0), (0, 0, 0), (0, 1, 0), (1, 1, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0)], #[(0, 0, 0), (0, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (0, 0, 0), (0, 1, 0), (1, 1, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (0, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], #[(0, 0, 0), (0, 0, 0), (1, 1, 0), (0, 1, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0)], #[(0, 0, 0), (0, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (0, 0, 0), (1, 1, 0), (0, 1, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (1, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], #[(0, 0, 0), (1, 0, 0), (0, 0, 0), (0, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0)], #[(0, 0, 0), (1, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (1, 0, 0), (0, 0, 0), (0, 0, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], #[(0, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0)], #[(0, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0)], #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)], #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0), (1, 0, 0)], #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (0, 0, 1), (1, 0, 1), (0, 1, 1), (1, 1, 1)], #[(0, 0, 0), (1, 0, 0), (1, 1, 0), (0, 1, 0), (1, 0, 1), (0, 0, 1), (1, 1, 1), (0, 1, 1)]]
def values (k : K) (x : B) : B :=
  (valueData.getD k.val #[]).getD (index x) 0

theorem value_injective : Function.Injective values := by native_decide
theorem value_zero : ∀ k, values k 0 = 0 := by native_decide
theorem value_maps : ∀ k i x, maps i (values k x) = values k (maps i x) := by native_decide
def representativeData : Array B := #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1)]
def representative (i : Fin 4) : B := representativeData.getD i.val 0
def transportData : Array (Fin 4 × Fin 8) := #[(0, 7), (1, 7), (2, 6), (2, 7), (3, 1), (3, 4), (3, 5), (3, 7)]
def transport (b : B) := transportData.getD (index b) (0, 0)
def choiceData : Array (Array B) := #[#[(0, 0, 0)], #[(0, 0, 0), (1, 0, 0)], #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (1, 1, 0)], #[(0, 0, 0), (1, 0, 0), (0, 0, 1), (1, 0, 1)]]
def sizes (i : Fin 4) : ℕ := (choiceData.getD i.val #[]).size
def choices (i : Fin 4) (q : Fin (sizes i)) : B := (choiceData.getD i.val #[]).getD q.val 0
def stabilizerData : Array (Array (Fin 8)) := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 6, 7], #[0, 2, 3, 6, 0, 0, 0, 0], #[0, 1, 0, 0, 0, 0, 0, 0]]
def stabilizers (i : Fin 4) (j : Fin 8) := (stabilizerData.getD i.val #[]).getD j.val 0
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

private def law690 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 2) (.Leaf 1)) (.Leaf 0))))⟩
private theorem count690 : Fintype.card {p : Params // ZeroTest (model p) law690} = 192 := by native_decide

private def law4275 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0))), (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 0)))⟩
private theorem count4275 : Fintype.card {p : Params // ZeroTest (model p) law4275} = 120 := by native_decide

end Magma.ProjectionVector3By8Upper

open Magma.ProjectionVector3By8Upper

theorem Equation4275_not_termStructuralFromFin_Equation690_projectionVector3By8Upper : ¬ Law4275.TermStructuralFromFin Law690 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law690) (fun p => ZeroTest (model p) law4275)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count690, count4275]
    decide

/-- info: 'Equation4275_not_termStructuralFromFin_Equation690_projectionVector3By8Upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 chart_choices._native.native_decide.ax_1_1,
 chart_covered._native.native_decide.ax_1_1,
 chart_fixed._native.native_decide.ax_1_1,
 chart_transport._native.native_decide.ax_1_1,
 map_add._native.native_decide.ax_1_1,
 map_zero._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count4275._native.native_decide.ax_1_1,
 count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4275_not_termStructuralFromFin_Equation690_projectionVector3By8Upper

