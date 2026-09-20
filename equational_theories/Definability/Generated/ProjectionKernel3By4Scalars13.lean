import equational_theories.Definability.ProjectionKernelCounting
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by translations, a projection, and kernel maps. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionKernel3By4Scalars13
abbrev A := ZMod 3
abbrev B := ZMod 4
abbrev K := Fin 8
def scalarData : Array B := #[1, 3]
def maps (i : Fin 2) : B →+ B where
  toFun x := scalarData[i.val]! * x
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]
def valueData : Array (Array B) := #[#[0, 0, 0, 0], #[0, 0, 2, 0], #[0, 1, 0, 3], #[0, 1, 2, 3], #[0, 2, 0, 2], #[0, 2, 2, 2], #[0, 3, 0, 1], #[0, 3, 2, 1]]
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

private def law690 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 2) (.Leaf 1)) (.Leaf 0))))⟩
private theorem count690 : Fintype.card {p : Params // ZeroTest (model p) law690} = 24 := by native_decide

private def law3321 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 0))))⟩
private theorem count3321 : Fintype.card {p : Params // ZeroTest (model p) law3321} = 12 := by native_decide

private def law3323 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Leaf 2))))⟩
private theorem count3323 : Fintype.card {p : Params // ZeroTest (model p) law3323} = 12 := by native_decide

private def law3520 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 0)) (.Leaf 2)))⟩
private theorem count3520 : Fintype.card {p : Params // ZeroTest (model p) law3520} = 12 := by native_decide

private def law3523 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 2)))⟩
private theorem count3523 : Fintype.card {p : Params // ZeroTest (model p) law3523} = 12 := by native_decide

private def law3524 : MagmaLaw (Fin 3) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 2)) (.Leaf 0)))⟩
private theorem count3524 : Fintype.card {p : Params // ZeroTest (model p) law3524} = 12 := by native_decide

end Magma.ProjectionKernel3By4Scalars13

open Magma.ProjectionKernel3By4Scalars13

theorem Equation3520_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13 : ¬ Law3520.TermStructuralFromFin Law690 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law690) (fun p => ZeroTest (model p) law3520)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count690, count3520]
    decide

/-- info: 'Equation3520_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count3520._native.native_decide.ax_1_1,
 count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3520_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13

theorem Equation3321_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13 : ¬ Law3321.TermStructuralFromFin Law690 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law690) (fun p => ZeroTest (model p) law3321)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count690, count3321]
    decide

/-- info: 'Equation3321_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count3321._native.native_decide.ax_1_1,
 count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3321_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13

theorem Equation3323_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13 : ¬ Law3323.TermStructuralFromFin Law690 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law690) (fun p => ZeroTest (model p) law3323)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count690, count3323]
    decide

/-- info: 'Equation3323_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count3323._native.native_decide.ax_1_1,
 count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3323_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13

theorem Equation3523_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13 : ¬ Law3523.TermStructuralFromFin Law690 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law690) (fun p => ZeroTest (model p) law3523)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count690, count3523]
    decide

/-- info: 'Equation3523_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count3523._native.native_decide.ax_1_1,
 count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3523_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13

theorem Equation3524_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13 : ¬ Law3524.TermStructuralFromFin Law690 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law690) (fun p => ZeroTest (model p) law3524)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 3 i))
  · rw [count690, count3524]
    decide

/-- info: 'Equation3524_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 value_coverage._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 count3524._native.native_decide.ax_1_1,
 count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3524_not_termStructuralFromFin_Equation690_projectionKernel3By4Scalars13

