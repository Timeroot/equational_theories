import equational_theories.Definability.Generated.DeepMatrixZ4Count55
import equational_theories.Definability.Generated.DeepMatrixZ4Count632
import equational_theories.Definability.Generated.DeepMatrixZ4Count642
import equational_theories.Definability.Generated.DeepMatrixZ4Count690
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

open Magma.DeepMatrixZ4

theorem Equation642_not_termStructuralFromFin_Equation690_deepMatrixCount : ¬ Law642.TermStructuralFromFin Law690 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := ZMod 4) (d := 2)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (ZMod 4) 2 => Test law690 p)
    (fun p : P (ZMod 4) 2 => Test law642 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count690, count642]
    decide

/-- info: 'Equation642_not_termStructuralFromFin_Equation690_deepMatrixCount' depends on axioms: [propext, Classical.choice, Quot.sound, count642._native.native_decide.ax_1_1, count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation642_not_termStructuralFromFin_Equation690_deepMatrixCount

theorem Equation55_not_termStructuralFromFin_Equation690_deepMatrixCount : ¬ Law55.TermStructuralFromFin Law690 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := ZMod 4) (d := 2)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (ZMod 4) 2 => Test law690 p)
    (fun p : P (ZMod 4) 2 => Test law55 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count690, count55]
    decide

/-- info: 'Equation55_not_termStructuralFromFin_Equation690_deepMatrixCount' depends on axioms: [propext, Classical.choice, Quot.sound, count55._native.native_decide.ax_1_1, count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation55_not_termStructuralFromFin_Equation690_deepMatrixCount

theorem Equation632_not_termStructuralFromFin_Equation690_deepMatrixCount : ¬ Law632.TermStructuralFromFin Law690 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := ZMod 4) (d := 2)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (ZMod 4) 2 => Test law690 p)
    (fun p : P (ZMod 4) 2 => Test law632 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count690, count632]
    decide

/-- info: 'Equation632_not_termStructuralFromFin_Equation690_deepMatrixCount' depends on axioms: [propext, Classical.choice, Quot.sound, count632._native.native_decide.ax_1_1, count690._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation632_not_termStructuralFromFin_Equation690_deepMatrixCount

