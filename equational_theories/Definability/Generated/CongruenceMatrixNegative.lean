import equational_theories.Definability.Generated.CongruenceMatrixCount1045
import equational_theories.Definability.Generated.CongruenceMatrixCount1632

open Law Law.MagmaLaw Magma.CongruenceMatrix Magma.CongruenceMatrixCounts

theorem Equation1045_not_termStructuralFromFin_Equation1632_congruenceMatrix :
    ¬ Law1045.TermStructuralFromFin Law1632 := by
  apply not_termStructuralFromFin_of_cloneFamily_count operation operation_injective
    (one, zero) (zero, one) composition operation_fst operation_snd operation_comp
    (fun p : Params => Test law1632 p) (fun p : Params => Test law1045 p)
  · intro p hp φ
    exact (test_iff_satisfies _ _).mp hp (fun i => φ i.val)
  · intro p hp
    apply (test_iff_satisfies _ _).mpr
    intro φ
    exact hp (fun i => φ (Fin.ofNat 2 i))
  · rw [count1632, count1045]
    decide

/-- info: 'Equation1045_not_termStructuralFromFin_Equation1632_congruenceMatrix' depends on axioms: [propext, Classical.choice, Quot.sound, count1045._native.native_decide.ax_1_1, count1632._native.native_decide.ax_1_1, Magma.CongruenceMatrix.decode_embed._native.native_decide.ax_1_1✝, Magma.CongruenceMatrix.lift_add._native.native_decide.ax_1_1✝, Magma.CongruenceMatrix.lift_mul_left._native.native_decide.ax_1_1✝, Magma.CongruenceMatrix.lift_mul_lift._native.native_decide.ax_1_1✝, Magma.CongruenceMatrix.lift_mul_right._native.native_decide.ax_1_1✝] -/
#guard_msgs (whitespace := lax) in
#print axioms Equation1045_not_termStructuralFromFin_Equation1632_congruenceMatrix
