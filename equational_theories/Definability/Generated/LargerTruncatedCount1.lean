import equational_theories.Definability.ScalarFamilyCounting
import equational_theories.Definability.TruncatedPolynomialRing

/-! Affine counts with cached multiplication kernels. -/
open Law Law.MagmaLaw Magma.ScalarFamily Magma.AffineFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law1122 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 1))) (.Leaf 0)))⟩
private theorem count1122 : count (R := (Magma.TruncatedPolynomial.T (ZMod 2) 8)) law1122 = 227328 := by native_decide

private def law1731 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count1731 : count (R := (Magma.TruncatedPolynomial.T (ZMod 2) 8)) law1731 = 227328 := by native_decide

private def law3253 : MagmaLaw (Fin 1) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count3253 : count (R := (Magma.TruncatedPolynomial.T (ZMod 2) 8)) law3253 = 196096 := by native_decide

theorem Equation3253_not_termStructuralFromFin_Equation1122_largerTruncatedCount : ¬ Law3253.TermStructuralFromFin Law1122 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 8))) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (Test law1122) (Test law3253)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 1 i))
  · rw [card_test, card_test, count1122, count3253]
    decide

/-- info: 'Equation3253_not_termStructuralFromFin_Equation1122_largerTruncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1122._native.native_decide.ax_1_1, count3253._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3253_not_termStructuralFromFin_Equation1122_largerTruncatedCount

theorem Equation3253_not_termStructuralFromFin_Equation1731_largerTruncatedCount : ¬ Law3253.TermStructuralFromFin Law1731 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 8))) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (Test law1731) (Test law3253)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 1 i))
  · rw [card_test, card_test, count1731, count3253]
    decide

/-- info: 'Equation3253_not_termStructuralFromFin_Equation1731_largerTruncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1731._native.native_decide.ax_1_1, count3253._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3253_not_termStructuralFromFin_Equation1731_largerTruncatedCount


