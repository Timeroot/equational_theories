import equational_theories.Definability.ProjectionBaseCounting
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by translations, a projection, and kernel maps. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionBase4By5Actions13And14
abbrev A := ZMod 4
abbrev B := ZMod 5
abbrev K := Fin 25
def scalarData : Array B := #[1, 4]
def maps (i : Fin 2) : B →+ B where
  toFun x := scalarData[i.val]! * x
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]
def valueData : Array (Array B) := #[#[0, 0, 0, 0, 0], #[0, 0, 1, 4, 0], #[0, 0, 2, 3, 0], #[0, 0, 3, 2, 0], #[0, 0, 4, 1, 0], #[0, 1, 0, 0, 4], #[0, 1, 1, 4, 4], #[0, 1, 2, 3, 4], #[0, 1, 3, 2, 4], #[0, 1, 4, 1, 4], #[0, 2, 0, 0, 3], #[0, 2, 1, 4, 3], #[0, 2, 2, 3, 3], #[0, 2, 3, 2, 3], #[0, 2, 4, 1, 3], #[0, 3, 0, 0, 2], #[0, 3, 1, 4, 2], #[0, 3, 2, 3, 2], #[0, 3, 3, 2, 2], #[0, 3, 4, 1, 2], #[0, 4, 0, 0, 1], #[0, 4, 1, 4, 1], #[0, 4, 2, 3, 1], #[0, 4, 3, 2, 1], #[0, 4, 4, 1, 1]]
def values (k : K) (x : B) : B :=
  (valueData.getD k.val #[]).getD x.val 0

theorem value_injective : Function.Injective values := by native_decide
theorem value_zero : ∀ k, values k 0 = 0 := by native_decide
theorem value_maps : ∀ k i x, maps i (values k x) = values k (maps i x) := by native_decide
def representativeData : Array B := #[0, 1, 2]
def representative (i : Fin 3) : B := representativeData.getD i.val 0
def transportData : Array (Fin 3 × Fin 2) := #[(0, 1), (1, 0), (2, 0), (2, 1), (1, 1)]
def transport (b : B) := transportData.getD b.val (0, 0)
def choiceData : Array (Array B) := #[#[0], #[0, 1, 2, 3, 4], #[0, 1, 2, 3, 4]]
def sizes (i : Fin 3) : ℕ := (choiceData.getD i.val #[]).size
def choices (i : Fin 3) (q : Fin (sizes i)) : B := (choiceData.getD i.val #[]).getD q.val 0
def stabilizerData : Array (Array (Fin 2)) := #[#[0, 1], #[0, 0], #[0, 0]]
def stabilizers (i : Fin 3) (j : Fin 2) := (stabilizerData.getD i.val #[]).getD j.val 0
theorem chart_transport : ∀ b, maps (transport b).2 (representative (transport b).1) = b := by native_decide
theorem chart_fixed : ∀ i j, maps (stabilizers i j) (representative i) = representative i := by native_decide
theorem chart_choices : ∀ i b, (representative i = 0 → b = 0) →
    (∀ j, maps (stabilizers i j) b = b) → ∃ q, choices i q = b := by native_decide
theorem chart_covered : ∀ p : (i : Fin 3) → Fin (sizes i), ∃ k, ∀ b,
    values k b = maps (transport b).2 (choices (transport b).1 (p (transport b).1)) := by native_decide
theorem value_coverage : ∀ f : B → B, f 0 = 0 →
    (∀ i x, maps i (f x) = f (maps i x)) → ∃ k, values k = f :=
  Magma.ProjectionKernelFamily.kernel_coverage_of_chart maps values representative transport
    sizes choices stabilizers chart_transport chart_fixed chart_choices chart_covered

def baseScalarData : Array A := #[1, 3]
def baseMaps (i : Fin 2) : A →+ A where
  toFun x := baseScalarData[i.val]! * x
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]
def gData : Array (Array A) := #[#[0, 0, 0, 0], #[0, 0, 2, 0], #[0, 1, 0, 3], #[0, 1, 2, 3], #[0, 2, 0, 2], #[0, 2, 2, 2], #[0, 3, 0, 1], #[0, 3, 2, 1], #[2, 0, 0, 0], #[2, 0, 2, 0], #[2, 1, 0, 3], #[2, 1, 2, 3], #[2, 2, 0, 2], #[2, 2, 2, 2], #[2, 3, 0, 1], #[2, 3, 2, 1]]
def gvalues (p : Fin 16) (a : A) : A := (gData.getD p.val #[]).getD a.val 0
def baseRepresentativeData : Array A := #[0, 1, 2]
def baseRepresentative (i : Fin 3) : A := baseRepresentativeData.getD i.val 0
def baseTransportData : Array (Fin 3 × Fin 2) := #[(0, 1), (1, 0), (2, 1), (1, 1)]
def baseTransport (a : A) := baseTransportData.getD a.val (0, 0)
def hvalues (q : Fin 3 → K) (a : A) : K := q (baseTransport a).1

theorem base_transport : ∀ a, baseMaps (baseTransport a).2 (baseRepresentative (baseTransport a).1) = a := by native_decide
theorem base_representative : ∀ i, (baseTransport (baseRepresentative i)).1 = i := by native_decide
theorem base_orbit : ∀ j a, (baseTransport a).1 = (baseTransport (baseMaps j a)).1 := by native_decide
theorem g_injective : Function.Injective gvalues := by native_decide
theorem g_maps : ∀ p j a, baseMaps j (gvalues p a) = gvalues p (baseMaps j a) := by native_decide
theorem g_coverage : ∀ g : A → A, (∀ j a, baseMaps j (g a) = g (baseMaps j a)) → ∃ p, gvalues p = g := by native_decide
theorem h_maps : ∀ q j a, hvalues q a = hvalues q (baseMaps j a) := by
  intro q j a
  exact congrArg q (base_orbit j a)
theorem h_injective : Function.Injective hvalues := by
  intro p q hpq
  funext i
  have h := congrFun hpq (baseRepresentative i)
  simpa only [hvalues, base_representative] using h
theorem h_coverage : ∀ h : A → K, (∀ j a, h a = h (baseMaps j a)) → ∃ q, hvalues q = h := by
  intro h hh
  refine ⟨fun i => h (baseRepresentative i), ?_⟩
  funext a
  have he := hh (baseTransport a).2 (baseRepresentative (baseTransport a).1)
  simpa only [base_transport] using he

abbrev Params := Fin 16 × (Fin 3 → K)
@[implicit_reducible] def model (p : Params) : Magma (A × B) :=
  Magma.ProjectionBaseFamily.fam values gvalues hvalues p

theorem translations (p : Params) (a : A × B) : (model p).IsEndo (fun x => a + x) :=
  Magma.ProjectionBaseFamily.family_generators maps values baseMaps gvalues hvalues
    value_zero value_maps g_maps h_maps p (.inl (.inl a))

private def law1443 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 2))))⟩
private theorem count1443 : Fintype.card {p : Params // ZeroTest (model p) law1443} = 189 := by native_decide

private def law3521 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count3521 : Fintype.card {p : Params // ZeroTest (model p) law3521} = 120 := by native_decide

private def law4314 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 0))), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 1)))⟩
private theorem count4314 : Fintype.card {p : Params // ZeroTest (model p) law4314} = 120 := by native_decide

end Magma.ProjectionBase4By5Actions13And14

open Magma.ProjectionBase4By5Actions13And14

theorem Equation3521_not_termStructuralFromFin_Equation1443_projectionBase4By5Actions13And14 : ¬ Law3521.TermStructuralFromFin Law1443 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionBaseFamily.gen maps baseMaps)
    model (Magma.ProjectionBaseFamily.family_injective values gvalues hvalues value_injective g_injective h_injective)
    (Magma.ProjectionBaseFamily.coverage maps values baseMaps gvalues hvalues value_injective value_coverage g_coverage h_coverage)
    (Magma.ProjectionBaseFamily.family_generators maps values baseMaps gvalues hvalues value_zero value_maps g_maps h_maps)
    (fun p => ZeroTest (model p) law1443) (fun p => ZeroTest (model p) law3521)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1443, count3521]
    decide

/-- info: 'Equation3521_not_termStructuralFromFin_Equation1443_projectionBase4By5Actions13And14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 base_orbit._native.native_decide.ax_1_1,
 base_representative._native.native_decide.ax_1_1,
 base_transport._native.native_decide.ax_1_1,
 chart_choices._native.native_decide.ax_1_1,
 chart_covered._native.native_decide.ax_1_1,
 chart_fixed._native.native_decide.ax_1_1,
 chart_transport._native.native_decide.ax_1_1,
 g_coverage._native.native_decide.ax_1_1,
 g_injective._native.native_decide.ax_1_1,
 g_maps._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count1443._native.native_decide.ax_1_1,
 count3521._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3521_not_termStructuralFromFin_Equation1443_projectionBase4By5Actions13And14

theorem Equation4314_not_termStructuralFromFin_Equation1443_projectionBase4By5Actions13And14 : ¬ Law4314.TermStructuralFromFin Law1443 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionBaseFamily.gen maps baseMaps)
    model (Magma.ProjectionBaseFamily.family_injective values gvalues hvalues value_injective g_injective h_injective)
    (Magma.ProjectionBaseFamily.coverage maps values baseMaps gvalues hvalues value_injective value_coverage g_coverage h_coverage)
    (Magma.ProjectionBaseFamily.family_generators maps values baseMaps gvalues hvalues value_zero value_maps g_maps h_maps)
    (fun p => ZeroTest (model p) law1443) (fun p => ZeroTest (model p) law4314)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1443, count4314]
    decide

/-- info: 'Equation4314_not_termStructuralFromFin_Equation1443_projectionBase4By5Actions13And14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 base_orbit._native.native_decide.ax_1_1,
 base_representative._native.native_decide.ax_1_1,
 base_transport._native.native_decide.ax_1_1,
 chart_choices._native.native_decide.ax_1_1,
 chart_covered._native.native_decide.ax_1_1,
 chart_fixed._native.native_decide.ax_1_1,
 chart_transport._native.native_decide.ax_1_1,
 g_coverage._native.native_decide.ax_1_1,
 g_injective._native.native_decide.ax_1_1,
 g_maps._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count1443._native.native_decide.ax_1_1,
 count4314._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation4314_not_termStructuralFromFin_Equation1443_projectionBase4By5Actions13And14

