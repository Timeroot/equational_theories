import equational_theories.Definability.MatrixFamilyCounting

/-! Generated matrix-family counting certificates. -/
open Law Law.MagmaLaw Magma.MatrixFamily
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

private def law667 : MagmaLaw (Fin 2) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Leaf 0) (.Fork (.Fork (.Leaf 0) (.Leaf 0)) (.Leaf 1))))⟩
private theorem count667 : Fintype.card {p : LP (ZMod 2) 3 // Test law667 (p.1, p.2, 0)} = 46 := by
  native_decide

private def law898 : MagmaLaw (Fin 3) := ⟨(.Leaf 0), (.Fork (.Leaf 1) (.Fork (.Fork (.Leaf 0) (.Leaf 2)) (.Fork (.Leaf 2) (.Leaf 1))))⟩
private theorem count898 : Fintype.card {p : LP (ZMod 2) 3 // Test law898 (p.1, p.2, 0)} = 49 := by
  native_decide

theorem Equation667_not_termStructuralFromFin_Equation898_deepMatrixCount : ¬ Law667.TermStructuralFromFin Law898 := by
  apply not_termStructuralFromFin_of_cloneFamily_count (lin (R := ZMod 2) (d := 3)) lin_injective
    (1, 0) (0, 1) linComp lin_fst lin_snd lin_comp
    (fun p : LP (ZMod 2) 3 => Test law898 (p.1, p.2, 0))
    (fun p : LP (ZMod 2) 3 => Test law667 (p.1, p.2, 0))
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count898, count667]
    decide

/-- info: 'Equation667_not_termStructuralFromFin_Equation898_deepMatrixCount' depends on axioms: [propext, Classical.choice, Quot.sound, count667._native.native_decide.ax_1_1, count898._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation667_not_termStructuralFromFin_Equation898_deepMatrixCount

