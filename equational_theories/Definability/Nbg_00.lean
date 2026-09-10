import equational_theories.Definability.Nbb_00
import equational_theories.Generated.VampireProven.Proofs11
import equational_theories.Definability.AutBox2
import equational_theories.Equations.All
import equational_theories.EquationLawConversion

open Law Law.MagmaLaw

theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4548 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4548 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4548_implies_Law4527 G M hM) GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4527
