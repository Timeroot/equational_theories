import equational_theories.Definability.Jax_02
import equational_theories.Definability.Jax_13
import equational_theories.Definability.Kax_04
import equational_theories.Definability.Kax_11
import equational_theories.Definability.Kax_17
import equational_theories.Definability.Kax_18
import equational_theories.Definability.Kax_19
import equational_theories.Definability.Kax_20
import equational_theories.Definability.Kax_21
import equational_theories.Definability.Kc_05
import equational_theories.Definability.Kd_09
import equational_theories.Definability.Kd_15
import equational_theories.Definability.Ke_15
import equational_theories.Definability.Ke_16
import equational_theories.Definability.Ke_18
import equational_theories.Definability.Ke_22
import equational_theories.Definability.Ke_24
import equational_theories.Definability.Lh_00
import equational_theories.Definability.Lw3_00
import equational_theories.Definability.Mna_00
import equational_theories.Definability.Ms_02
import equational_theories.Definability.Ms_03
import equational_theories.Definability.Q2x_01
import equational_theories.Definability.Wka_00
import equational_theories.Generated.MagmaEgg.small._001
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zy
import equational_theories.Generated.VampireProven.Proofs1
import equational_theories.Generated.VampireProven.Proofs10
import equational_theories.Generated.VampireProven.Proofs2
import equational_theories.Definability.AutBox2
import equational_theories.Equations.All
import equational_theories.EquationLawConversion

open Law Law.MagmaLaw

theorem GuardAut2_pyy_x_x_y_x_x_pyx_Equation1042 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1042 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law1042_implies_Law844 G M hM) GuardAut2_pyy_x_x_y_x_x_pyx_Equation844

theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation106 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law106 :=
  AutBox.guardAut2_mono (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law106_implies_Law834 G M hM) GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation834

theorem GuardAut2_pyy_x_x_y_x_x_pyx_Equation1060 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1060 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law1060_implies_Law844 G M hM) GuardAut2_pyy_x_x_y_x_x_pyx_Equation844

theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation1068 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1068 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law1068_implies_Law1049 G M hM) GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation1049

theorem GuardAut2_pyy_x_x_y_x_x_pyx_Equation109 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law109 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law109_implies_Law844 G M hM) GuardAut2_pyy_x_x_y_x_x_pyx_Equation844

theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation111 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law111 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law111_implies_Law1049 G M hM) GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation1049

theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation1246 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1246 :=
  AutBox.guardAut2_mono (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law1246_implies_Law834 G M hM) GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation834

theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation1247 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1247 :=
  AutBox.guardAut2_mono (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law1247_implies_Law834 G M hM) GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation834

theorem GuardAut2_pyy_x_x_y_x_x_pyx_Equation1257 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1257 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law1257_implies_Law844 G M hM) GuardAut2_pyy_x_x_y_x_x_pyx_Equation844

theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation1261 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1261 :=
  AutBox.guardAut2_mono (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law1261_implies_Law834 G M hM) GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation834

theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation1265 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1265 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law1265_implies_Law1049 G M hM) GuardAut2_pxx_x_pyy_y_pxy_pxx_pyx_Equation1049

theorem GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation1506 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1506 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law1506_implies_Law72 G M hM) GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation72

theorem GuardAut2_pxy_x_pyx_y_x_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law1560_implies_Law916 G M hM) GuardAut2_pxy_x_pyx_y_x_x_pyx_Equation916

theorem GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation1560 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1560 :=
  AutBox.guardAut2_mono (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law1560_implies_Law960 G M hM) GuardAut2_x_y_pxx_y_pxx_x_pxy_Equation960

theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2536 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2536 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law2536_implies_Law2712 G M hM) GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation2712

theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation3503 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3503 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law3503_implies_Law3499 G M hM) GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation3499

theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3558 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3558 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law3558_implies_Law3456 G M hM) GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3456

theorem GuardAut2_pyy_x_pxx_y_y_x_pxy_Equation3744 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3744 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law3744_implies_Law326 G M hM) GuardAut2_pyy_x_pxx_y_y_x_pxy_Equation326

theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation3869 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3869 :=
  AutBox.guardAut2_of_triv (L' := Law1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) rfl GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation1

theorem GuardAut2_pxx_y_pxx_x_x_pyy_pxy_Equation3929 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3929 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law3929_implies_Law4381 G M hM) GuardAut2_pxx_y_pxx_x_x_pyy_pxy_Equation4381

theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3951 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3951 :=
  AutBox.guardAut2_of_triv (L' := Law1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) rfl GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation1

theorem GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation4297 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4297 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4297_implies_Law4290 G M hM) GuardAut2_pxx_x_pyy_y_pxy_x_pyx_Equation4290

theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4419 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4419 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4419_implies_Law4411 G M hM) GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4411

theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4426 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4426 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4426_implies_Law4410 G M hM) GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4410

theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4427 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4427 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4427_implies_Law4411 G M hM) GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4411

theorem GuardAut2_pxx_y_pxx_x_x_pyy_pxy_Equation4434 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4434 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4434_implies_Law4381 G M hM) GuardAut2_pxx_y_pxx_x_x_pyy_pxy_Equation4381

theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4441 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4441 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4441_implies_Law4437 G M hM) GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4437

theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4447 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4447 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4447_implies_Law4434 G M hM) GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4434

theorem GuardAut2_pyx_y_x_y_pxx_pyx_pxy_Equation4448 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4448 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4448_implies_Law4456 G M hM) GuardAut2_pyx_y_x_y_pxx_pyx_pxy_Equation4456

theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4463 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4463 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4463_implies_Law4447 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4447

theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4463 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4463 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4463_implies_Law4434 G M hM) GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4434

theorem GuardAut2_pyx_y_x_y_pxx_pyx_pxy_Equation4464 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4464 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4464_implies_Law4456 G M hM) GuardAut2_pyx_y_x_y_pxx_pyx_pxy_Equation4456

theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4509 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4509 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4509_implies_Law4397 G M hM) GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4397

theorem GuardAut2_pxy_y_x_y_pxx_pxy_pyx_Equation4514 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4514 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4514_implies_Law4401 G M hM) GuardAut2_pxy_y_x_y_pxx_pxy_pyx_Equation4401

theorem GuardAut2_pxy_y_x_y_pxx_pxy_pyx_Equation4518 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4518 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4518_implies_Law4401 G M hM) GuardAut2_pxy_y_x_y_pxx_pxy_pyx_Equation4401

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4527 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4527 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4527_implies_Law4423 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4423

theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4535 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4535 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4535_implies_Law4411 G M hM) GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4411

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4548 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4548 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4548_implies_Law4423 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4423

theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4552 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4552 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4552_implies_Law4411 G M hM) GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4411

theorem GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation4559 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4559 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4559_implies_Law4490 G M hM) GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation4490

theorem GuardAut2_pyx_y_pxx_y_pxx_y_pxy_Equation4559 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4559 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4559_implies_Law4416 G M hM) GuardAut2_pyx_y_pxx_y_pxx_y_pxy_Equation4416

theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4562 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4562 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4562_implies_Law4411 G M hM) GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4411

theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4567 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4567 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4567_implies_Law4411 G M hM) GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4411

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4572 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4572 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4572_implies_Law4423 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4423

theorem GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4577 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4577 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4577_implies_Law4411 G M hM) GuardAut2_pxy_y_pxx_y_pxx_y_pyx_Equation4411

theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation4633 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4633 :=
  AutBox.guardAut2_of_triv (L' := Law1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) rfl GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation1

theorem GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law723_implies_Law72 G M hM) GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation72

theorem GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation841 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law841 :=
  AutBox.guardAut2_mono (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law841_implies_Law834 G M hM) GuardAut2_x_y_pxy_x_pxx_y_pxy_Equation834

theorem GuardAut2_pyy_x_x_y_x_x_pyx_Equation849 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law849 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law849_implies_Law844 G M hM) GuardAut2_pyy_x_x_y_x_x_pyx_Equation844

theorem GuardAut2_pyy_x_x_y_x_x_pyx_Equation851 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law851 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law851_implies_Law844 G M hM) GuardAut2_pyy_x_x_y_x_x_pyx_Equation844

theorem GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation909 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law909 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law909_implies_Law72 G M hM) GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation72

theorem GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law947 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law947_implies_Law72 G M hM) GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation72

theorem GuardAut2_pxy_x_pyx_y_x_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law960_implies_Law916 G M hM) GuardAut2_pxy_x_pyx_y_x_x_pyx_Equation916
