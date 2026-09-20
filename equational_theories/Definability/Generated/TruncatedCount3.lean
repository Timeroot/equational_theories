import equational_theories.Definability.TruncatedPolynomialRing
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law835 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 0)) (.Fork (.Leaf 1) (.Leaf 0))))⟩
private theorem count835 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law835 (p.1, p.2, 0)} = 3 := by
  native_decide

private def law842 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 1)) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count842 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law842 (p.1, p.2, 0)} = 3 := by
  native_decide

private def law861 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 2)) (.Fork (.Leaf 2) (.Leaf 1))))⟩
private theorem count861 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law861 (p.1, p.2, 0)} = 5 := by
  native_decide

private def law3712 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 0) (.Leaf 1)))⟩
private theorem count3712 : Fintype.card {p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law3712 (p.1, p.2, 0)} = 4 := by
  native_decide

theorem Equation3712_not_termStructuralFromFin_Equation861_truncatedCount : ¬ Law3712.TermStructuralFromFin Law861 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := (Magma.TruncatedPolynomial.T (ZMod 2) 4)) (d := 1)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law861 (p.1, p.2, 0))
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law3712 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count861, count3712]
    decide

/-- info: 'Equation3712_not_termStructuralFromFin_Equation861_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3712._native.native_decide.ax_1_1, count861._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3712_not_termStructuralFromFin_Equation861_truncatedCount

theorem Equation835_not_termStructuralFromFin_Equation861_truncatedCount : ¬ Law835.TermStructuralFromFin Law861 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := (Magma.TruncatedPolynomial.T (ZMod 2) 4)) (d := 1)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law861 (p.1, p.2, 0))
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law835 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count861, count835]
    decide

/-- info: 'Equation835_not_termStructuralFromFin_Equation861_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count835._native.native_decide.ax_1_1, count861._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation835_not_termStructuralFromFin_Equation861_truncatedCount

theorem Equation842_not_termStructuralFromFin_Equation861_truncatedCount : ¬ Law842.TermStructuralFromFin Law861 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := (Magma.TruncatedPolynomial.T (ZMod 2) 4)) (d := 1)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law861 (p.1, p.2, 0))
    (fun p : LP (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law842 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count861, count842]
    decide

/-- info: 'Equation842_not_termStructuralFromFin_Equation861_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count842._native.native_decide.ax_1_1, count861._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation842_not_termStructuralFromFin_Equation861_truncatedCount

