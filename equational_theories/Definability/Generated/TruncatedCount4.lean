import equational_theories.Definability.TruncatedPolynomialRing
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law500 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0)))))⟩
private theorem count500 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 5) 1 // Test law500 p} = 2560 := by
  native_decide

private def law3261 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem count3261 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 5) 1 // Test law3261 p} = 2432 := by
  native_decide

private def law3306 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 1))))⟩
private theorem count3306 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 5) 1 // Test law3306 p} = 2432 := by
  native_decide

theorem Equation3306_not_termStructuralFromFin_Equation500_truncatedCount : ¬ Law3306.TermStructuralFromFin Law500 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 5)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 5) 1 => Test law500 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 5) 1 => Test law3306 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count500, count3306]
    decide

/-- info: 'Equation3306_not_termStructuralFromFin_Equation500_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3306._native.native_decide.ax_1_1, count500._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3306_not_termStructuralFromFin_Equation500_truncatedCount

theorem Equation3261_not_termStructuralFromFin_Equation500_truncatedCount : ¬ Law3261.TermStructuralFromFin Law500 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 5)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 5) 1 => Test law500 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 5) 1 => Test law3261 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count500, count3261]
    decide

/-- info: 'Equation3261_not_termStructuralFromFin_Equation500_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3261._native.native_decide.ax_1_1, count500._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3261_not_termStructuralFromFin_Equation500_truncatedCount

