import equational_theories.Definability.Lo3_04
import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem GuardAut3_pxy_x_pxy_y_x_y_y_x_pxx_pxy_Equation2536 :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2536 :=
  GuardAut3_pxy_x_pxy_y_x_y_y_x_pxx_pxy_all Law2536
