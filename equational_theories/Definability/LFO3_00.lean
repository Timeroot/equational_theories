import equational_theories.Definability.Reversible

/-!
# Normal forms for deep-guard companions

Each case tree below is pointwise equal to the original operation or its
opposite. Splitting its two guards proves that equality directly; the shared
normal-form lemma then supplies the automorphism obligation for any source.
The theorem names are retained for compatibility with existing certificates.
These short proofs replace the original superposition replays.
-/

open Law Law.MagmaLaw FreeMagma

theorem GuardAut2_ppxxpxy_y_x_y_pxy_pxx_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 0) ⋆ (Lf 1))) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  apply AutBox.guardAut2_of_eq_op
  intro G M a b
  classical
  rw [AutBox.iteOf2_apply]
  simp only [evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp_all

theorem GuardAut2_ppxxpyy_y_pxy_y_pxy_y_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ ((Lf 1) ⋆ (Lf 1))) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  apply AutBox.guardAut2_of_eq_op
  intro G M a b
  classical
  rw [AutBox.iteOf2_apply]
  simp only [evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp_all

theorem GuardAut2_ppxxx_ppyxy_x_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 0)) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  apply AutBox.guardAut2_of_eq_opposite
  intro G M a b
  classical
  rw [AutBox.iteOf2_apply]
  simp only [evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp_all

theorem GuardAut2_ppxxx_ppyyx_x_y_pyx_pxx_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  apply AutBox.guardAut2_of_eq_opposite
  intro G M a b
  classical
  rw [AutBox.iteOf2_apply]
  simp only [evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp_all

theorem GuardAut2_ppxxx_ppyyy_pyx_x_pyx_x_pyx_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) (((Lf 1) ⋆ (Lf 1)) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1 := by
  apply AutBox.guardAut2_of_eq_opposite
  intro G M a b
  classical
  rw [AutBox.iteOf2_apply]
  simp only [evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp_all

theorem GuardAut2_ppxxx_pyx_pxx_y_pxy_x_pxy_Equation1 :
    AutBox.GuardAut2 (((Lf 0) ⋆ (Lf 0)) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  apply AutBox.guardAut2_of_eq_op
  intro G M a b
  classical
  rw [AutBox.iteOf2_apply]
  simp only [evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp_all

/-- info: Checked 6 normal-form proofs: only the standard Lean axioms. -/
#guard_msgs in
run_elab do
  let names : List Lean.Name := [
    ``GuardAut2_ppxxpxy_y_x_y_pxy_pxx_pxy_Equation1,
    ``GuardAut2_ppxxpyy_y_pxy_y_pxy_y_pxy_Equation1,
    ``GuardAut2_ppxxx_ppyxy_x_y_pyx_pxx_pyx_Equation1,
    ``GuardAut2_ppxxx_ppyyx_x_y_pyx_pxx_pyx_Equation1,
    ``GuardAut2_ppxxx_ppyyy_pyx_x_pyx_x_pyx_Equation1,
    ``GuardAut2_ppxxx_pyx_pxx_y_pxy_x_pxy_Equation1]
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name}: unexpected axiom {ax}"
  Lean.logInfo "Checked 6 normal-form proofs: only the standard Lean axioms."
