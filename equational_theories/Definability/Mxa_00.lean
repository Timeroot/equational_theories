import equational_theories.Definability.Lo3_05
import equational_theories.Definability.Lo3_07
import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem GuardAut3_pxy_x_x_y_pxy_pyy_pyy_pxx_x_pxy_Equation1506 :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1506 :=
  GuardAut3_pxy_x_x_y_pxy_pyy_pyy_pxx_x_pxy_all Law1506

theorem GuardAut3_pyx_x_x_y_pxx_pyx_pxx_pxy_x_pyx_Equation1560 :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 :=
  GuardAut3_pyx_x_x_y_pxx_pyx_pxx_pxy_x_pyx_all Law1560

theorem GuardAut3_pxy_x_x_y_pxx_pxy_pxx_pyx_x_pxy_Equation2055 :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2055 :=
  GuardAut3_pxy_x_x_y_pxx_pxy_pxx_pyx_x_pxy_all Law2055

theorem GuardAut3_pyx_x_x_y_pxx_pyx_pxx_pxy_x_pyx_Equation947 :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law947 :=
  GuardAut3_pyx_x_x_y_pxx_pyx_pxx_pxy_x_pyx_all Law947

theorem GuardAut3_pyx_x_x_y_pxx_pyx_pxx_pyx_x_pyx_Equation960 :
    AutBox.GuardAut3 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 :=
  GuardAut3_pyx_x_x_y_pxx_pyx_pxx_pyx_x_pyx_all Law960
