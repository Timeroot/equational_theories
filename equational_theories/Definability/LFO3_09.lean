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

theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1 := by
  apply AutBox.guardAut2_of_eq_op
  intro G M a b
  classical
  rw [AutBox.iteOf2_apply]
  simp only [evalInMagma, Matrix.cons_val_zero, Matrix.cons_val_one]
  split_ifs <;> simp_all

/-- info: Checked 1 normal-form proofs: only the standard Lean axioms. -/
#guard_msgs in
run_elab do
  let names : List Lean.Name := [
    ``GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation1]
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless ax ∈ [``propext, ``Classical.choice, ``Quot.sound] do
        throwError "{name}: unexpected axiom {ax}"
  Lean.logInfo "Checked 1 normal-form proofs: only the standard Lean axioms."
