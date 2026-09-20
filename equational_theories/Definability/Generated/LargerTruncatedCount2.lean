import equational_theories.Definability.ScalarFamilyCounting
import equational_theories.Definability.TruncatedPolynomialRing

/-! Affine counts with cached multiplication kernels. -/
open Law Law.MagmaLaw Magma.ScalarFamily Magma.AffineFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law643 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 1))))⟩
private theorem count643 : count (R := (Magma.TruncatedPolynomial.T (ZMod 7) 3)) law643 = 2402 := by native_decide

private def law1637 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count1637 : count (R := (Magma.TruncatedPolynomial.T (ZMod 7) 3)) law1637 = 1374 := by native_decide

private def law3712 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 0) (.Leaf 1)))⟩
private theorem count3712 : count (R := (Magma.TruncatedPolynomial.T (ZMod 7) 3)) law3712 = 688 := by native_decide

private def law3721 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 0) (.Leaf 0)))⟩
private theorem count3721 : count (R := (Magma.TruncatedPolynomial.T (ZMod 7) 3)) law3721 = 693 := by native_decide

theorem Equation1637_not_termStructuralFromFin_Equation643_largerTruncatedCount : ¬ Law1637.TermStructuralFromFin Law643 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 7) 3))) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (Test law643) (Test law1637)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [card_test, card_test, count643, count1637]
    decide

/-- info: 'Equation1637_not_termStructuralFromFin_Equation643_largerTruncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1637._native.native_decide.ax_1_1, count643._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1637_not_termStructuralFromFin_Equation643_largerTruncatedCount

theorem Equation3712_not_termStructuralFromFin_Equation643_largerTruncatedCount : ¬ Law3712.TermStructuralFromFin Law643 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 7) 3))) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (Test law643) (Test law3712)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [card_test, card_test, count643, count3712]
    decide

/-- info: 'Equation3712_not_termStructuralFromFin_Equation643_largerTruncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3712._native.native_decide.ax_1_1, count643._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3712_not_termStructuralFromFin_Equation643_largerTruncatedCount

theorem Equation3721_not_termStructuralFromFin_Equation643_largerTruncatedCount : ¬ Law3721.TermStructuralFromFin Law643 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 7) 3))) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (Test law643) (Test law3721)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [card_test, card_test, count643, count3721]
    decide

/-- info: 'Equation3721_not_termStructuralFromFin_Equation643_largerTruncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3721._native.native_decide.ax_1_1, count643._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3721_not_termStructuralFromFin_Equation643_largerTruncatedCount


