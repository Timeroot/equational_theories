import equational_theories.Definability.Nac_02
import equational_theories.Definability.Nag_03
import equational_theories.Definability.Nan_00
import equational_theories.Definability.Naq_02
import equational_theories.Definability.Naq_05
import equational_theories.Definability.Nas_04
import equational_theories.Definability.Nas_06
import equational_theories.Definability.Nau_00
import equational_theories.Definability.Nau_01
import equational_theories.Definability.Nau_02
import equational_theories.Definability.Nau_03
import equational_theories.Definability.Nay_00
import equational_theories.Definability.Nay_01
import equational_theories.Definability.Nay_02
import equational_theories.Definability.Nba_00
import equational_theories.Generated.MagmaEgg.small._002
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_uw_wz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_wz_zx
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_yx_zy
import equational_theories.Generated.SimpleRewrites.theorems.Rewrite_zy
import equational_theories.Generated.VampireProven.Proofs11
import equational_theories.Generated.VampireProven.Proofs13
import equational_theories.Generated.VampireProven.Proofs4
import equational_theories.Generated.VampireProven.Proofs6
import equational_theories.Definability.AutBox2
import equational_theories.Equations.All
import equational_theories.EquationLawConversion

open Law Law.MagmaLaw

theorem GuardAut2_pxy_x_pxy_pyy_pxy_y_pxy_Equation1506 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1506 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law1506_implies_Law723 G M hM) GuardAut2_pxy_x_pxy_pyy_pxy_y_pxy_Equation723

theorem GuardAut2_pxx_y_pyx_pyy_x_pyy_pyx_Equation2055 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2055 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law2055_implies_Law2656 G M hM) GuardAut2_pxx_y_pyx_pyy_x_pyy_pyx_Equation2656

theorem GuardAut2_pxx_y_pxy_y_pxy_pyx_pxy_Equation224 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law224 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law224_implies_Law2702 G M hM) GuardAut2_pxx_y_pxy_y_pxy_pyx_pxy_Equation2702

theorem GuardAut2_pyx_x_pxx_y_y_pxy_pyx_Equation2774 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2774 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law2774_implies_Law2306 G M hM) GuardAut2_pyx_x_pxx_y_y_pxy_pyx_Equation2306

theorem GuardAut2_pyx_x_pyx_pyy_y_x_pyx_Equation373 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law373 :=
  AutBox.guardAut2_mono ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law373_implies_Law366 G M hM) GuardAut2_pyx_x_pyx_pyy_y_x_pyx_Equation366

theorem GuardAut2_pxx_y_pxy_y_x_pxx_pyx_Equation3791 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3791 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law3791_implies_Law4197 G M hM) GuardAut2_pxx_y_pxy_y_x_pxx_pyx_Equation4197

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4391 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4391 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4391_implies_Law4388 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4388

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4424 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4424 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4424_implies_Law4388 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4388

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4428 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4428 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4428_implies_Law4388 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4388

theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4430 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4430_implies_Law4425 G M hM) GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4425

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4460 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4460 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4460_implies_Law4388 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4388

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4461 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4461 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4461_implies_Law4388 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4388

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4464 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4464 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4464_implies_Law4388 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4388

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4497 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4497 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4497_implies_Law4388 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4388

theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4519 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4519 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4519_implies_Law4507 G M hM) GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4507

theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4519 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4519 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4519_implies_Law4507 G M hM) GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4507

theorem GuardAut2_pxy_x_pyx_pyy_pyy_y_pyx_Equation4522 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4522 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4522_implies_Law4517 G M hM) GuardAut2_pxy_x_pyx_pyy_pyy_y_pyx_Equation4517

theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4527 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4527 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4527_implies_Law4572 G M hM) GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation4572

theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4564 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4564 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law4564_implies_Law4546 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4546

theorem GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4574 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4574 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law4574_implies_Law4388 G M hM) GuardAut2_pxx_y_pyy_y_x_x_pyx_Equation4388

theorem GuardAut2_pxx_pxy_pxx_y_pxx_x_pyx_Equation765 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law765 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law765_implies_Law778 G M hM) GuardAut2_pxx_pxy_pxx_y_pxx_x_pyx_Equation778

theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_x_pyx_Equation947 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law947 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} M hM ↦ @Law947_implies_Law723 G M hM) GuardAut2_pxx_pxy_pxx_pyx_pyx_x_pyx_Equation723

theorem GuardAut2_pxy_x_pxy_pyy_pxy_y_pxy_Equation947 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law947 :=
  AutBox.guardAut2_mono ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} M hM ↦ @Law947_implies_Law723 G M hM) GuardAut2_pxy_x_pxy_pyy_pxy_y_pxy_Equation723
