import equational_theories.Definability.TruncatedPolynomialRing
import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law614 : MagmaLaw (Fin 1) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Leaf 0))))⟩
private theorem count614 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law614 p} = 144 := by
  native_decide

private def law817 : MagmaLaw (Fin 1) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Fork (.Leaf 0) (.Leaf 0))))⟩
private theorem count817 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law817 p} = 144 := by
  native_decide

private def law861 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 1) (.Leaf 2)) (.Fork (.Leaf 2) (.Leaf 1))))⟩
private theorem count861 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law861 p} = 65 := by
  native_decide

private def law1026 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Fork (.Leaf 1) (.Leaf 0))) (.Leaf 1)))⟩
private theorem count1026 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law1026 p} = 264 := by
  native_decide

private def law1682 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Fork (.Leaf 1) (.Leaf 0)) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Leaf 1)))⟩
private theorem count1682 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law1682 p} = 256 := by
  native_decide

private def law3721 : MagmaLaw (Fin 2) := ⟨(.Fork (.Leaf 0) (.Leaf 1)), (.Fork (.Fork (.Leaf 0) (.Leaf 1)) (.Fork (.Leaf 0) (.Leaf 0)))⟩
private theorem count3721 : Fintype.card {p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 // Test law3721 p} = 36 := by
  native_decide

theorem Equation3721_not_termStructuralFromFin_Equation861_truncatedCount : ¬ Law3721.TermStructuralFromFin Law861 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 4)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law861 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law3721 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count861, count3721]
    decide

/-- info: 'Equation3721_not_termStructuralFromFin_Equation861_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count3721._native.native_decide.ax_1_1, count861._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation3721_not_termStructuralFromFin_Equation861_truncatedCount

theorem Equation614_not_termStructuralFromFin_Equation1026_truncatedCount : ¬ Law614.TermStructuralFromFin Law1026 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 4)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law1026 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law614 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 1 i))
  · rw [count1026, count614]
    decide

/-- info: 'Equation614_not_termStructuralFromFin_Equation1026_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1026._native.native_decide.ax_1_1, count614._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_termStructuralFromFin_Equation1026_truncatedCount

theorem Equation817_not_termStructuralFromFin_Equation1026_truncatedCount : ¬ Law817.TermStructuralFromFin Law1026 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 4)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law1026 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law817 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 1 i))
  · rw [count1026, count817]
    decide

/-- info: 'Equation817_not_termStructuralFromFin_Equation1026_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1026._native.native_decide.ax_1_1, count817._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_termStructuralFromFin_Equation1026_truncatedCount

theorem Equation614_not_termStructuralFromFin_Equation1682_truncatedCount : ¬ Law614.TermStructuralFromFin Law1682 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 4)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law1682 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law614 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 1 i))
  · rw [count1682, count614]
    decide

/-- info: 'Equation614_not_termStructuralFromFin_Equation1682_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1682._native.native_decide.ax_1_1, count614._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation614_not_termStructuralFromFin_Equation1682_truncatedCount

theorem Equation817_not_termStructuralFromFin_Equation1682_truncatedCount : ¬ Law817.TermStructuralFromFin Law1682 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (op (R := (Magma.TruncatedPolynomial.T (ZMod 2) 4)) (d := 1)) op_injective
    (1, 0, 0) (0, 1, 0) comp op_fst op_snd op_comp
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law1682 p)
    (fun p : P (Magma.TruncatedPolynomial.T (ZMod 2) 4) 1 => Test law817 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 1 i))
  · rw [count1682, count817]
    decide

/-- info: 'Equation817_not_termStructuralFromFin_Equation1682_truncatedCount' depends on axioms: [propext, Classical.choice, Quot.sound, count1682._native.native_decide.ax_1_1, count817._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation817_not_termStructuralFromFin_Equation1682_truncatedCount

