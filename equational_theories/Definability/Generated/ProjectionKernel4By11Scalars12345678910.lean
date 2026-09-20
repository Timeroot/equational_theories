import DefOrbit.Generated.NativeProjectionKernel4By11Scalars12345678910
import equational_theories.Definability.NativeOrbitCounting
import equational_theories.Definability.ProjectionKernelCounting
import Mathlib.Data.ZMod.Basic

/-! A complete family preserved by translations, a projection, and kernel maps. -/
open Law Law.MagmaLaw Magma.InvariantFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Magma.ProjectionKernel4By11Scalars12345678910
abbrev A := ZMod 4
abbrev B := ZMod 11
abbrev K := Fin 11
def scalarData : Array B := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def maps (i : Fin 10) : B →+ B where
  toFun x := scalarData[i.val]! * x
  map_zero' := by simp
  map_add' := by intros; simp [mul_add]
def valueData : Array (Array B) := #[#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], #[0, 2, 4, 6, 8, 10, 1, 3, 5, 7, 9], #[0, 3, 6, 9, 1, 4, 7, 10, 2, 5, 8], #[0, 4, 8, 1, 5, 9, 2, 6, 10, 3, 7], #[0, 5, 10, 4, 9, 3, 8, 2, 7, 1, 6], #[0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5], #[0, 7, 3, 10, 6, 2, 9, 5, 1, 8, 4], #[0, 8, 5, 2, 10, 7, 4, 1, 9, 6, 3], #[0, 9, 7, 5, 3, 1, 10, 8, 6, 4, 2], #[0, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]]
def values (k : K) (x : B) : B :=
  (valueData.getD k.val #[]).getD x.val 0

theorem value_injective : Function.Injective values := by native_decide
theorem value_zero : ∀ k, values k 0 = 0 := by native_decide
theorem value_maps : ∀ k i x, maps i (values k x) = values k (maps i x) := by native_decide
def representativeData : Array B := #[0, 1]
def representative (i : Fin 2) : B := representativeData.getD i.val 0
def transportData : Array (Fin 2 × Fin 10) := #[(0, 9), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)]
def transport (b : B) := transportData.getD b.val (0, 0)
def choiceData : Array (Array B) := #[#[0], #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]]
def sizes (i : Fin 2) : ℕ := (choiceData.getD i.val #[]).size
def choices (i : Fin 2) (q : Fin (sizes i)) : B := (choiceData.getD i.val #[]).getD q.val 0
def stabilizerData : Array (Array (Fin 10)) := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def stabilizers (i : Fin 2) (j : Fin 10) := (stabilizerData.getD i.val #[]).getD j.val 0
theorem chart_transport : ∀ b, maps (transport b).2 (representative (transport b).1) = b := by native_decide
theorem chart_fixed : ∀ i j, maps (stabilizers i j) (representative i) = representative i := by native_decide
theorem chart_choices : ∀ i b, (representative i = 0 → b = 0) →
    (∀ j, maps (stabilizers i j) b = b) → ∃ q, choices i q = b := by native_decide
theorem chart_covered : ∀ p : (i : Fin 2) → Fin (sizes i), ∃ k, ∀ b,
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

def paramEquiv : Params ≃ (Fin 256 × Fin 14641) :=
  Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv
def codeEquiv : Params ≃ Fin 3748096 :=
  paramEquiv.trans ((Equiv.prodComm _ _).trans (finProdFinEquiv (m := 14641) (n := 256)))
private theorem native_g_correct : ∀ (i : Fin 256) (x : A),
    DefOrbit.NativeProjectionKernel4By11Scalars12345678910.g i.val x = finFunctionFinEquiv.symm i x := by native_decide
private theorem native_h_correct : ∀ (i : Fin 14641) (x : A),
    DefOrbit.NativeProjectionKernel4By11Scalars12345678910.h i.val x = finFunctionFinEquiv.symm i x := by native_decide
private theorem native_value_correct : ∀ (i : K) (x : B),
    DefOrbit.NativeProjectionKernel4By11Scalars12345678910.value i x = values i x := by native_decide
private theorem native_op_correct (i : Fin 256 × Fin 14641) (x y : A × B) :
    DefOrbit.NativeProjectionKernel4By11Scalars12345678910.op i.1.val i.2.val x y = (model (paramEquiv.symm i)).op x y := by
  simp only [DefOrbit.NativeProjectionKernel4By11Scalars12345678910.op, native_g_correct, native_h_correct, native_value_correct]
  rfl
private theorem native_code_mod (i : Fin 256 × Fin 14641) :
    (i.1.val + 256 * i.2.val) % 256 = i.1.val := by omega
private theorem native_code_div (i : Fin 256 × Fin 14641) :
    (i.1.val + 256 * i.2.val) / 256 = i.2.val := by omega

private def law446 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 2) (.Fork (.Leaf 0) (.Leaf 0)))))⟩
private theorem native_good446_correct (code : Nat) :
    DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good446 code = true ↔ DefOrbit.NativeProjectionKernel4By11Scalars12345678910.test446 (code % 256) (code / 256) := by
  simp [DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good446, DefOrbit.NativeProjectionKernel4By11Scalars12345678910.test446, DefOrbit.NativeProjectionKernel4By11Scalars12345678910.points, List.all_eq_true, Prod.forall]
private theorem native_test446_correct (i : Fin 256 × Fin 14641) :
    DefOrbit.NativeProjectionKernel4By11Scalars12345678910.test446 i.1.val i.2.val ↔ ZeroTest (model (paramEquiv.symm i)) law446 := by
  unfold DefOrbit.NativeProjectionKernel4By11Scalars12345678910.test446 ZeroTest law446
  simp only [native_op_correct, FreeMagma.evalInMagma, Fin.forall_fin_succ_pi,
    Fin.forall_fin_zero_pi, Fin.cons_zero]
  rfl
private theorem native_count446 :
    DefOrbit.countBelow DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good446 3748096 = 6306 := by native_decide
private theorem count446 : Fintype.card {p : Params // ZeroTest (model p) law446} = 6306 := by
  rw [DefOrbit.card_eq_countBelow codeEquiv
    (fun p => ZeroTest (model p) law446) DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good446]
  · exact native_count446
  · intro p
    change ZeroTest (model p) law446 ↔
      DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good446 ((paramEquiv p).1.val + 256 * (paramEquiv p).2.val) = true
    rw [native_good446_correct, native_code_mod, native_code_div]
    simpa only [Equiv.symm_apply_apply] using (native_test446_correct (paramEquiv p)).symm

private def law3258 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem native_good3258_correct (code : Nat) :
    DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good3258 code = true ↔ DefOrbit.NativeProjectionKernel4By11Scalars12345678910.test3258 (code % 256) (code / 256) := by
  simp [DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good3258, DefOrbit.NativeProjectionKernel4By11Scalars12345678910.test3258, DefOrbit.NativeProjectionKernel4By11Scalars12345678910.points, List.all_eq_true, Prod.forall]
private theorem native_test3258_correct (i : Fin 256 × Fin 14641) :
    DefOrbit.NativeProjectionKernel4By11Scalars12345678910.test3258 i.1.val i.2.val ↔ ZeroTest (model (paramEquiv.symm i)) law3258 := by
  unfold DefOrbit.NativeProjectionKernel4By11Scalars12345678910.test3258 ZeroTest law3258
  simp only [native_op_correct, FreeMagma.evalInMagma, Fin.forall_fin_succ_pi,
    Fin.forall_fin_zero_pi, Fin.cons_zero]
  rfl
private theorem native_count3258 :
    DefOrbit.countBelow DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good3258 3748096 = 5656 := by native_decide
private theorem count3258 : Fintype.card {p : Params // ZeroTest (model p) law3258} = 5656 := by
  rw [DefOrbit.card_eq_countBelow codeEquiv
    (fun p => ZeroTest (model p) law3258) DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good3258]
  · exact native_count3258
  · intro p
    change ZeroTest (model p) law3258 ↔
      DefOrbit.NativeProjectionKernel4By11Scalars12345678910.good3258 ((paramEquiv p).1.val + 256 * (paramEquiv p).2.val) = true
    rw [native_good3258_correct, native_code_mod, native_code_div]
    simpa only [Equiv.symm_apply_apply] using (native_test3258_correct (paramEquiv p)).symm

end Magma.ProjectionKernel4By11Scalars12345678910

open Magma.ProjectionKernel4By11Scalars12345678910

theorem Equation3258_not_termStructuralFromFin_Equation446_projectionKernel4By11Scalars12345678910 : ¬ Law3258.TermStructuralFromFin Law446 := by
  apply Magma.InvariantFamily.not_termStructuralFromFin (Magma.ProjectionKernelFamily.gen (A := A) maps)
    model (Magma.ProjectionKernelFamily.family_injective values value_injective)
    (Magma.ProjectionKernelFamily.coverage maps values value_coverage)
    (Magma.ProjectionKernelFamily.family_generators maps values value_zero value_maps)
    (fun p => ZeroTest (model p) law446) (fun p => ZeroTest (model p) law3258)
  · intro p hp φ
    exact (zeroTest_iff_satisfies (model p) (translations p) _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (zeroTest_iff_satisfies (model p) (translations p) _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count446, count3258]
    decide

/-- info: 'Equation3258_not_termStructuralFromFin_Equation446_projectionKernel4By11Scalars12345678910' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 chart_choices._native.native_decide.ax_1_1,
 chart_covered._native.native_decide.ax_1_1,
 chart_fixed._native.native_decide.ax_1_1,
 chart_transport._native.native_decide.ax_1_1,
 value_injective._native.native_decide.ax_1_1,
 value_maps._native.native_decide.ax_1_1,
 value_zero._native.native_decide.ax_1_1,
 native_count3258._native.native_decide.ax_1_1,
 native_count446._native.native_decide.ax_1_1,
 native_g_correct._native.native_decide.ax_1_1,
 native_h_correct._native.native_decide.ax_1_1,
 native_value_correct._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3258_not_termStructuralFromFin_Equation446_projectionKernel4By11Scalars12345678910

