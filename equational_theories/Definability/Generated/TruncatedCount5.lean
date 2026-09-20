import equational_theories.Definability.TruncatedPolynomialRing
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law56 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 1))))⟩
private theorem count56 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 3) 3) 1 // Test law56 p} = 82 := by
  native_decide

private def law3721 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 0) (.Leaf 0)))⟩
private theorem count3721 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 3) 3) 1 // Test law3721 p} = 57 := by
  native_decide

theorem Equation3721_not_termStructuralFromFin_Equation56_truncatedCount : ¬ Law3721.TermStructuralFromFin Law56 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 3) 3)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 3) 3) 1 => Test law56 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 3) 3) 1 => Test law3721 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count56, count3721]
    decide

/-- info: 'Equation3721_not_termStructuralFromFin_Equation56_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3721._native.native_decide.ax_1_1, count56._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3721_not_termStructuralFromFin_Equation56_truncatedCount

