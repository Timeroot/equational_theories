import equational_theories.Definability.Lo5_00
import equational_theories.Definability.AutBox3
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem GuardAut3_pxx_pxy_pyx_pyy_pxx_pyx_pxx_pxy_pyy_pyx_Equation3509 :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3509 :=
  GuardAut3_pxx_pxy_pyx_pyy_pxx_pyx_pxx_pxy_pyy_pyx_all Law3509

theorem GuardAut3_pxx_pxy_pyx_pyy_pxx_pyx_pxx_pxy_pyy_pyx_Equation3515 :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3515 :=
  GuardAut3_pxx_pxy_pyx_pyy_pxx_pyx_pxx_pxy_pyy_pyx_all Law3515

theorem GuardAut3_pxx_pyx_pxy_pyy_pxx_pxy_pxx_pyx_pyy_pxy_Equation3928 :
    AutBox.GuardAut3 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3928 :=
  GuardAut3_pxx_pyx_pxy_pyy_pxx_pxy_pxx_pyx_pyy_pxy_all Law3928
