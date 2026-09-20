import equational_theories.Definability.TruncatedPolynomialRing
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law477 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Fork (.Leaf 1) (.Leaf 1)))))⟩
private theorem count477 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 // Test law477 p} = 32 := by
  native_decide

private def law823 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 0) (.Leaf 1))))⟩
private theorem count823 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 // Test law823 p} = 10 := by
  native_decide

private def law861 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 2)) (.Fork (.Leaf 2) (.Leaf 1))))⟩
private theorem count861 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 // Test law861 p} = 17 := by
  native_decide

private def law1038 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Leaf 1))) (.Leaf 0)))⟩
private theorem count1038 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 // Test law1038 p} = 29 := by
  native_decide

private def law1226 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Leaf 1)) (.Leaf 1)))⟩
private theorem count1226 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 // Test law1226 p} = 12 := by
  native_decide

theorem Equation1038_not_termStructuralFromFin_Equation477_truncatedCount : ¬ Law1038.TermStructuralFromFin Law477 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 3)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 => Test law477 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 => Test law1038 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count477, count1038]
    decide

/-- info: 'Equation1038_not_termStructuralFromFin_Equation477_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1038._native.native_decide.ax_1_1, count477._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1038_not_termStructuralFromFin_Equation477_truncatedCount

theorem Equation823_not_termStructuralFromFin_Equation861_truncatedCount : ¬ Law823.TermStructuralFromFin Law861 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 3)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 => Test law861 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 => Test law823 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count861, count823]
    decide

/-- info: 'Equation823_not_termStructuralFromFin_Equation861_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count823._native.native_decide.ax_1_1, count861._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation823_not_termStructuralFromFin_Equation861_truncatedCount

theorem Equation1226_not_termStructuralFromFin_Equation861_truncatedCount : ¬ Law1226.TermStructuralFromFin Law861 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 3)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 => Test law861 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 3) 1 => Test law1226 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count861, count1226]
    decide

/-- info: 'Equation1226_not_termStructuralFromFin_Equation861_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1226._native.native_decide.ax_1_1, count861._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1226_not_termStructuralFromFin_Equation861_truncatedCount

