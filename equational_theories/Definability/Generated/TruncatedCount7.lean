import equational_theories.Definability.TruncatedPolynomialRing
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law56 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 1))))⟩
private theorem count56 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 // Test law56 (p.1, p.2, 0)} = 10 := by
  native_decide

private def law75 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem count75 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 // Test law75 (p.1, p.2, 0)} = 729 := by
  native_decide

private def law1637 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Leaf 0)))⟩
private theorem count1637 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 // Test law1637 (p.1, p.2, 0)} = 6 := by
  native_decide

private def law3253 : MagmaLaw (Fin 1) := ⟨(.Fork (.Leaf 0) (.Leaf 0)), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count3253 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 // Test law3253 (p.1, p.2, 0)} = 513 := by
  native_decide

private def law3712 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 0) (.Leaf 1)))⟩
private theorem count3712 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 // Test law3712 (p.1, p.2, 0)} = 4 := by
  native_decide

theorem Equation1637_not_termStructuralFromFin_Equation56_truncatedCount : ¬ Law1637.TermStructuralFromFin Law56 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := (Magma.TruncatedPolynomial.T (ZMod 3) 4)) (d := 1)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 => Test law56 (p.1, p.2, 0))
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 => Test law1637 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count56, count1637]
    decide

/-- info: 'Equation1637_not_termStructuralFromFin_Equation56_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1637._native.native_decide.ax_1_1, count56._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1637_not_termStructuralFromFin_Equation56_truncatedCount

theorem Equation3712_not_termStructuralFromFin_Equation56_truncatedCount : ¬ Law3712.TermStructuralFromFin Law56 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := (Magma.TruncatedPolynomial.T (ZMod 3) 4)) (d := 1)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 => Test law56 (p.1, p.2, 0))
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 => Test law3712 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count56, count3712]
    decide

/-- info: 'Equation3712_not_termStructuralFromFin_Equation56_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3712._native.native_decide.ax_1_1, count56._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3712_not_termStructuralFromFin_Equation56_truncatedCount

theorem Equation3253_not_termStructuralFromFin_Equation75_truncatedCount : ¬ Law3253.TermStructuralFromFin Law75 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := (Magma.TruncatedPolynomial.T (ZMod 3) 4)) (d := 1)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 => Test law75 (p.1, p.2, 0))
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 3) 4) 1 => Test law3253 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 1 i))
  · rw [count75, count3253]
    decide

/-- info: 'Equation3253_not_termStructuralFromFin_Equation75_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3253._native.native_decide.ax_1_1, count75._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3253_not_termStructuralFromFin_Equation75_truncatedCount

