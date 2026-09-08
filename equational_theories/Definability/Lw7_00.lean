import equational_theories.Definability.Lo4_10
import equational_theories.Definability.Lo4_16
import equational_theories.Definability.Lo4_17
import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem GuardAut3_pxy_x_x_y_pxy_y_y_pxx_x_pxy_Equation2536 :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2536 :=
  GuardAut3_pxy_x_x_y_pxy_y_y_pxx_x_pxy_all Law2536

theorem GuardAut3_x_y_pxx_pxy_pxy_x_pxx_x_pxx_pxy_Equation2656 :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2656 :=
  GuardAut3_x_y_pxx_pxy_pxy_x_pxx_x_pxx_pxy_all Law2656

theorem GuardAut3_x_y_pxx_pyx_pyx_x_pxx_x_pxx_pyx_Equation723 :
    AutBox.GuardAut3 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 :=
  GuardAut3_x_y_pxx_pyx_pyx_x_pxx_x_pxx_pyx_all Law723
