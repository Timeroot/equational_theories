import equational_theories.Definability.Lf_15
import equational_theories.Definability.Lf_20
import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2712

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3180 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3180 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3180

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation433 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law433 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law433

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law854 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law854
