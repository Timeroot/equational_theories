import equational_theories.Definability.TruncatedPolynomialRing
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law477 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 1)))))⟩
private theorem count477 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 // Test law477 (p.1, p.2, 0)} = 4 := by
  native_decide

private def law3472 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Leaf 1)))⟩
private theorem count3472 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 // Test law3472 (p.1, p.2, 0)} = 3 := by
  native_decide

theorem Equation3472_not_termStructuralFromFin_Equation477_truncatedCount : ¬ Law3472.TermStructuralFromFin Law477 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := (Magma.TruncatedPolynomial.T (ZMod 2) 3)) (d := 1)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 => Test law477 (p.1, p.2, 0))
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 => Test law3472 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count477, count3472]
    decide

/-- info: 'Equation3472_not_termStructuralFromFin_Equation477_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3472._native.native_decide.ax_1_1, count477._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3472_not_termStructuralFromFin_Equation477_truncatedCount

