import equational_theories.Definability.TruncatedPolynomialRing
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law1434 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem count1434 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 3) 1 // Test law1434 (p.1, p.2, 0)} = 14 := by
  native_decide

private def law1525 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count1525 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 3) 1 // Test law1525 (p.1, p.2, 0)} = 18 := by
  native_decide

theorem Equation1434_not_termStructuralFromFin_Equation1525_truncatedCount : ¬ Law1434.TermStructuralFromFin Law1525 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := (Magma.TruncatedPolynomial.T (ZMod 3) 3)) (d := 1)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 3) 1 => Test law1525 (p.1, p.2, 0))
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 3) 1 => Test law1434 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1525, count1434]
    decide

/-- info: 'Equation1434_not_termStructuralFromFin_Equation1525_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1434._native.native_decide.ax_1_1, count1525._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1434_not_termStructuralFromFin_Equation1525_truncatedCount

