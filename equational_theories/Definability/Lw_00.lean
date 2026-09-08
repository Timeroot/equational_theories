import equational_theories.Definability.Lf_08
import equational_theories.Definability.Lf_10
import equational_theories.Definability.Lf_15
import equational_theories.Definability.Lf_16
import equational_theories.Definability.Lf_20
import equational_theories.Definability.Lf_21
import equational_theories.Definability.Lf_25
import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1021 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1021 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law1021

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1031 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1031 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1031

theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation1050 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1050 :=
  GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_all Law1050

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1050 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1050 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law1050

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1055 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1055

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1056 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1056 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law1056

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1064 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1064 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1064

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1064 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1064 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1064

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation1068 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1068 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law1068

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1068 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1068 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1068

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1068 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1068 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law1068

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1068 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1068 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1068

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation1090 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1090 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law1090

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1090 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1090 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law1090

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1101 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1101 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law1101

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1101 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1101 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1101

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1101 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1101 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1101

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1240 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1240 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1240

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1246 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1246 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1246

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1247 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1247 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law1247

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1247 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1247 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1247

theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation1255 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1255 :=
  GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_all Law1255

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1257 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1257 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1257

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1257 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1257 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1257

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1258 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1258 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1258

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1261 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1261 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law1261

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1261 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1261 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1261

theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation1263 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1263 :=
  GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_all Law1263

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation1265 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1265 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law1265

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1265 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1265 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1265

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1265 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1265 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law1265

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1265 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1265 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1265

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1271 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1271 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1271

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1271 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1271 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1271

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1334 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1334 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1334

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1384 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1384 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1384

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1430 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1430 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law1430

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1435 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1435 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law1435

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation1489 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1489 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law1489

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1506 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1506 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law1506

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1537 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1537 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1537

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1560 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law1560

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1571 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1571 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1571

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1630 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1630

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1633 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1633 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1633

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation166 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law166 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law166

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1726 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1726 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1726

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1726 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1726 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1726

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation1740 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1740 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law1740

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1740 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1740 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1740

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1740 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1740 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1740

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation1761 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1761 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law1761

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1761 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1761 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law1761

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation1774 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1774 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law1774

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1774 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1774 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law1774

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1845 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1845

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1884 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1884 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1884

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation1902 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1902 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law1902

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1902 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1902 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1902

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1902 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1902 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1902

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1910 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1910 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1910

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1910 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1910 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1910

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1929 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1929 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1929

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1929 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1929 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1929

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1958 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1958 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1958

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1964 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1964 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law1964

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1964 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law1964

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2055 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2055

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2062 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2062 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2062

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation208 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law208 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law208

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2097 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2097 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2097

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2105 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2105 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2105

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2113 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2113 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2113

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2134 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2134 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2134

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2161 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2161 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2161

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation218 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law218 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law218

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation224 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law224 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law224

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2263 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2263

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2273 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2273

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation23 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law23 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law23

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2308 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2308 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2308

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2310 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2310 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2310

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2319 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2319 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2319

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2322 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2322 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2322

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2322 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2322 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2322

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2327 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2327 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2327

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2333 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2333 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2333

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2333 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2333 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2333

theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation2351 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2351 :=
  GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all Law2351

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2355 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2355 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2355

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2355 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2355 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2355

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2364 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2364 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2364

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2376 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2376 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2376

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2376 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2376 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2376

theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation2385 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2385 :=
  GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all Law2385

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2389 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2389 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2389

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2389 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2389 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2389

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2402 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2402 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2402

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2402 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2402 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2402

theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation2406 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2406 :=
  GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all Law2406

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation242 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law242 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law242

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation242 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law242 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law242

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law242 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law242

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation242 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law242 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law242

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2420 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2420 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2420

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2420 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2420 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2420

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation2420 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2420 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law2420

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2420 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2420 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2420

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2425 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2425

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2425 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2425 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2425

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation2425 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2425 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law2425

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2425 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2425 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2425

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2430 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2430 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2430

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2430 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2430

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2446 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2446 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2446

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2452 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2452

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation246 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law246 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law246

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation246 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law246 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law246

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2476 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2476 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2476

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2493 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2493 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2493

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2517 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2517 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2517

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation2517 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2517 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law2517

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2552 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2552 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2552

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2552 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2552 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2552

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2554 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2554 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2554

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2554 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2554 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2554

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation2554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2554 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law2554

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2554 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2554

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2558 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2558 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2558

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2558 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2558 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2558

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation257 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law257 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law257

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation257 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law257 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law257

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2571 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2571 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2571

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation2571 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2571 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law2571

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation258 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law258 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law258

theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation2592 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2592 :=
  GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all Law2592

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2602 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2602 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2602

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2602 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2602 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2602

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2602 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2602 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2602

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2605 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2605 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2605

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2605 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2605 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2605

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2609 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2609 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2609

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2623 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2623 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2623

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2623 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2623 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2623

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation2623 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2623 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law2623

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2623 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2623 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2623

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation263 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law263 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law263

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation263 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law263 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law263

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2655 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2655 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2655

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2655 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2655 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2655

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2656 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2656 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2656

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation266 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law266 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law266

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation266 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law266 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law266

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2663 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2663 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2663

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2666 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2666 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2666

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2683 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2683 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2683

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2683 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2683 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2683

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2691 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2691 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2691

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2691 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2691 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2691

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2706 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2706 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2706

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2714 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2714 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2714

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2714 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2714 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2714

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2724 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2724 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2724

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2724 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2724

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law2725

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2725 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2725

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2725 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2725

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation273 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law273 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law273

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2733 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2733 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2733

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2739 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2739

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2739 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2739 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2739

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2741 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2741 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2741

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2741 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2741 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2741

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2755 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2755 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2755

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2761 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2761 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2761

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2761 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2761 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2761

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2770 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2770 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2770

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2779 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2779 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2779

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2779 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2779 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2779

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2782 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2782 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law2782

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2782 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2782 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2782

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2789 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2789 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2789

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2791 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2791 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2791

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2791 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2791 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2791

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2795 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2795 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2795

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2795 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2795 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2795

theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation280 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law280 :=
  GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_all Law280

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation283 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law283 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law283

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2836 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2836 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2836

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2836 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2836 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2836

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2858 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2858 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2858

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2858 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2858 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2858

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2860 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2860 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2860

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2868 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2868 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2868

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2868 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2868 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2868

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2890 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2890 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2890

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2890 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2890 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2890

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2894 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2894 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2894

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2894 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2894 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2894

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2899 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2899 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2899

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2919 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2919 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law2919

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2936 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2936 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2936

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2939 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2939 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2939

theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation2949 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2949 :=
  GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all Law2949

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2964 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2964 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2964

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2964 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2964 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2964

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2998 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2998 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law2998

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation2998 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2998 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law2998

theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation3007 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3007 :=
  GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_all Law3007

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3011 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3011 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3011

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3011 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3011 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3011

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3078 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3078 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3078

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3078 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3078 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3078

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3081 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3081 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3081

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3081 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3081 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3081

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3089 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3089 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3089

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3089 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3089 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3089

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3097 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3097 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3097

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3097 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3097 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3097

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation31 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law31 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law31

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation31 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law31 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law31

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3142 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3142 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3142

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3145 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3145 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3145

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3147 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3147 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3147

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3147 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3147 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3147

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3167 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3167 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3167

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3167 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3167 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3167

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3182 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3182 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3182

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3182 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3182 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3182

theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation3201 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3201 :=
  GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all Law3201

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation321 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law321 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law321

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3214 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3214 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3214

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3214 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3214 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3214

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3266 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3266 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3266

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3266 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3266 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3266

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3272 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3272 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3272

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation329 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law329 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law329

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation332 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law332 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law332

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation335 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law335 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law335

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3474 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3474 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law3474

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3482 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3482 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law3482

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3483 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3483

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3484 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3484 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law3484

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3484 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3484 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3484

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3486 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3486 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3486

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3490 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3490 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3490

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3490 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3490 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3490

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3494 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3494 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3494

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3494 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3494 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3494

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3498 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3498 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3498

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3498 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3498 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3498

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3501 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3501 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3501

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3502 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3502 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3502

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3505 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3505 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3505

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3505 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3505 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3505

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3506 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3506

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3506 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3506 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3506

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3507 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3507 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3507

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3507 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3507 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3507

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3548 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3548 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law3548

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3566 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3566 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3566

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3583 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3583 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3583

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3588 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3588 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law3588

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation359 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law359 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law359

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation359 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law359 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law359

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation361 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law361 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law361

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation361 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law361 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law361

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation363 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law363 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law363

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3634 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3634 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3634

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3634 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3634 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3634

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation365 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law365 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law365

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation365 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law365 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law365

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation366 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law366 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law366

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation367 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law367 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law367

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation367 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law367 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law367

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3690 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3690 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law3690

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3715 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3715 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3715

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law373 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law373

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3735 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3735 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3735

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3738 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3738 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3738

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3738 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3738 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3738

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3738 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3738 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3738

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3738 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3738 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3738

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation375 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law375 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law375

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation375 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law375 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law375

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3755 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3755 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3755

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3755 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3755 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3755

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3758 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3758 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3758

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation377 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law377 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law377

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation377 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law377 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law377

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation378 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law378 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law378

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation378 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law378 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law378

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3798 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3798 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3798

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3798 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3798 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3798

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3798 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3798 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3798

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3798 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3798 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3798

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation381 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law381 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law381

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation381 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law381 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law381

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation384 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law384 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law384

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation385 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law385 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law385

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation385 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law385 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law385

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3863 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3863 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3863

theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation3863 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3863 :=
  GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_all Law3863

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3866 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3866 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3866

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3868 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3868 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law3868

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3869 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3869 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3869

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3869 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3869 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3869

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation387 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law387 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law387

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3871 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3871 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law3871

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3871 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3871 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3871

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3872 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3872 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3872

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3875 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3875 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3875

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3876 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3876 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3876

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3876 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3876 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3876

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3878 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3878 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law3878

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3879 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3879 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3879

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3881 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3881 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law3881

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3882 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3882 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3882

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3882 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3882 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3882

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3885 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3885 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3885

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3885 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3885 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3885

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3886 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3886 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3886

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3886 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3886 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3886

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3889 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3889 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3889

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3889 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3889 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3889

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3892 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3892 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3892

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3896 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3896 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3896

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3896 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3896 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3896

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3899 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3899 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3899

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3899 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3899 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3899

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3900 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3900 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3900

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3900 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3900 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3900

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3904 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3904

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3904 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3904

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3907 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3907 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3907

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3908 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3908 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3908

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3911 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3911 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3911

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3911 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3911 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3911

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3912 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3912 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3912

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3912 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3912 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3912

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3913 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3913 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3913

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3913 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3913 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3913

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3919 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3919 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3919

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3919 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3919 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3919

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3926 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3926 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3926

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3926 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3926 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3926

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3929 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3929 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3929

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3929 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3929 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3929

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3930 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3930 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3930

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3933 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3933 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law3933

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3933 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3933 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law3933

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation3933 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3933 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law3933

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3933 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3933 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law3933

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3954 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3954 :=
  GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_all Law3954

theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation3964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3964 :=
  GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_all Law3964

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation4091 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4091 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law4091

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation4096 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4096 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law4096

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation4096 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4096 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law4096

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation4345 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4345 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law4345

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation4371 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4371 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law4371

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation442 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law442 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law442

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation4439 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4439 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law4439

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation444 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law444 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law444

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation444 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law444 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law444

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation4476 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4476 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law4476

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation4507 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4507 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law4507

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation4508 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4508 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law4508

theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation452 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law452 :=
  GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_all Law452

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation454 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law454 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law454

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation454 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law454 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law454

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation4542 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4542 :=
  GuardAut2_pxy_x_pxy_y_y_x_pxy_all Law4542

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation4608 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4608 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law4608

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law4610

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation4660 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4660 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law4660

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation4686 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4686 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law4686

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation50 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law50 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law50

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation53 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law53 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law53

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation543 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law543 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law543

theorem GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_Equation56 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law56 :=
  GuardAut2_pxx_x_pyy_y_pxy_pxy_pyx_all Law56

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation58 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law58 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law58

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation58 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law58 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law58

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation615 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law615 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law615

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation621 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law621 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law621

theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation624 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law624 :=
  GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all Law624

theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation626 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law626 :=
  GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_all Law626

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation633 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law633 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law633

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation649 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law649 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law649

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation649 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law649 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law649

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation661 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law661 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law661

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation661 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law661 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law661

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation723 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law723 :=
  GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_all Law723

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation821 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law821 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law821

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law840 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law840

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation840 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law840 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law840

theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation841 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law841 :=
  GuardAut2_pyx_x_pyx_y_y_x_pyx_all Law841

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation841 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law841 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law841

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation849 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law849 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law849

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation849 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law849 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law849

theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation850 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law850 :=
  GuardAut2_pxy_y_pxy_x_x_y_pxy_all Law850

theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation850 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law850 :=
  GuardAut2_pyx_y_pyx_x_x_y_pyx_all Law850
