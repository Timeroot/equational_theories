import equational_theories.Definability.Prn_prn6h2a
import equational_theories.Definability.Prn_prn6h2a_L14
import equational_theories.Definability.Prn_prn6h3a
import equational_theories.Definability.Prn_prn6h3a_L66
import equational_theories.Definability.Prn_prn6h3a_L115
import equational_theories.Definability.Prn_prn6h3a_L168
import equational_theories.Definability.Prn_prn6h3a_L873
import equational_theories.Definability.Prn_prn6h3a_L1117
import equational_theories.Definability.Prn_prn6h3a_L1483
import equational_theories.Definability.Prn_prn6h3a_L1485
import equational_theories.Definability.Prn_prn6h3a_L1486
import equational_theories.Definability.Prn_prn6h3a_L3620
import equational_theories.Definability.Prn_prn6h3a_L4369
import equational_theories.Definability.Prn_prn7h5a
import equational_theories.Definability.Prn_prn7h5a_L667
import equational_theories.Definability.Prn_prn7h5a_L870
import equational_theories.Definability.Prn_prn7h5a_L917
import equational_theories.Definability.Prn_prn7h5a_L978
import equational_theories.Definability.Prn_prn7h6a
import equational_theories.Definability.Prn_prn7h6a_L1076
import equational_theories.Definability.Prn_prn8h7a
import equational_theories.Definability.Prn_prn8h7a_L66
import equational_theories.Definability.Prn_prn8h7a_L1719
import equational_theories.Definability.Prn_prn8h8a
import equational_theories.Definability.Prn_prn8h8a_L313
import equational_theories.Definability.Prn_prn8h8a_L335
import equational_theories.Definability.Prn_prn8h8a_L1519
import equational_theories.Definability.Prn_prn8h8a_L1682
import equational_theories.Definability.Prn_prn8h8a_L3352
import equational_theories.Definability.Prn_prn8h8a_L3472
import equational_theories.Definability.Prn_prn8h8a_L3558
import equational_theories.Definability.Prn_prn8h8a_L3588
import equational_theories.Definability.Prn_prn8h8a_L4273
import equational_theories.Definability.Prn_prn8h8a_L4405
import equational_theories.Definability.Prn_prn8h8c
import equational_theories.Definability.Prn_prn8h8c_L3345
import equational_theories.Definability.Prn_prn8h8c_L3548
import equational_theories.Definability.Prn_prn8h8b
import equational_theories.Definability.Prn_prn8h8b_L335
import equational_theories.Definability.Prn_prn8h8b_L3352
import equational_theories.Definability.Prn_prn8h8b_L3555
import equational_theories.Definability.Prn_prn8h8b_L3748

/-!
# Refutations from a symmetry group whose invariant family is too large to enumerate

The other symmetry refutations in this directory all end in a walk of the invariant family, and
that is what bounds them: `Definability/AutModels.lean` gets as far as `Fin 13` only because
`AGL(1, 13)` leaves thirteen invariant operations behind. The models here have small automorphism
groups on carriers of six to nine elements, so their families run from five million upwards, and no
enumeration was ever going to finish.

It does not have to. An invariant operation is built one orbit value at a time, and a partial
choice already decides most instances of the target law -- an instance decided the wrong way kills
every completion of that choice at once. `Law.MagmaLaw.not_definableFrom_transportSearch` is that
search, and the trees it explores are some five orders of magnitude smaller than the families they
cover.
-/

open Law Law.MagmaLaw

theorem Equation14_not_definableFrom_Equation1480 :
    ¬ Law14.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h2aM1480 : Magma (Fin 6)) prn6h2aM1480_models
    prn6h2a.E prn6h2a.Einv prn6h2a.rep prn6h2a.tr prn6h2a.z prn6h2a.st (Magma.envs 6 2)
    ordprn6h2a_Law14 prn6h2a.hl prn6h2a.hr prn6h2aM1480_endo prn6h2a.htr prn6h2a.hz prn6h2a.hst
    noprn6h2a_Law14

theorem Equation66_not_definableFrom_Equation1480 :
    ¬ Law66.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 2)
    ordprn6h3a_Law66 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law66

theorem Equation115_not_definableFrom_Equation1480 :
    ¬ Law115.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 2)
    ordprn6h3a_Law115 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law115

theorem Equation168_not_definableFrom_Equation1480 :
    ¬ Law168.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 3)
    ordprn6h3a_Law168 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law168

theorem Equation873_not_definableFrom_Equation1480 :
    ¬ Law873.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 2)
    ordprn6h3a_Law873 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law873

theorem Equation1117_not_definableFrom_Equation1480 :
    ¬ Law1117.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 3)
    ordprn6h3a_Law1117 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law1117

theorem Equation1483_not_definableFrom_Equation1480 :
    ¬ Law1483.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 3)
    ordprn6h3a_Law1483 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law1483

theorem Equation1485_not_definableFrom_Equation1480 :
    ¬ Law1485.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 3)
    ordprn6h3a_Law1485 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law1485

theorem Equation1486_not_definableFrom_Equation1480 :
    ¬ Law1486.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 3)
    ordprn6h3a_Law1486 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law1486

theorem Equation3620_not_definableFrom_Equation1480 :
    ¬ Law3620.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 3)
    ordprn6h3a_Law3620 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law3620

theorem Equation4369_not_definableFrom_Equation1480 :
    ¬ Law4369.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn6h3aM1480 : Magma (Fin 6)) prn6h3aM1480_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 3)
    ordprn6h3a_Law4369 prn6h3a.hl prn6h3a.hr prn6h3aM1480_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law4369

theorem Equation66_not_definableFrom_Equation1719 :
    ¬ Law66.DefinableFrom Law1719 :=
  not_definableFrom_transportSearch (prn6h3aM1719 : Magma (Fin 6)) prn6h3aM1719_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 2)
    ordprn6h3a_Law66 prn6h3a.hl prn6h3a.hr prn6h3aM1719_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law66

theorem Equation115_not_definableFrom_Equation1719 :
    ¬ Law115.DefinableFrom Law1719 :=
  not_definableFrom_transportSearch (prn6h3aM1719 : Magma (Fin 6)) prn6h3aM1719_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 2)
    ordprn6h3a_Law115 prn6h3a.hl prn6h3a.hr prn6h3aM1719_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law115

theorem Equation873_not_definableFrom_Equation1719 :
    ¬ Law873.DefinableFrom Law1719 :=
  not_definableFrom_transportSearch (prn6h3aM1719 : Magma (Fin 6)) prn6h3aM1719_models
    prn6h3a.E prn6h3a.Einv prn6h3a.rep prn6h3a.tr prn6h3a.z prn6h3a.st (Magma.envs 6 2)
    ordprn6h3a_Law873 prn6h3a.hl prn6h3a.hr prn6h3aM1719_endo prn6h3a.htr prn6h3a.hz prn6h3a.hst
    noprn6h3a_Law873

theorem Equation667_not_definableFrom_Equation481 :
    ¬ Law667.DefinableFrom Law481 :=
  not_definableFrom_transportSearch (prn7h5aM481 : Magma (Fin 7)) prn7h5aM481_models
    prn7h5a.E prn7h5a.Einv prn7h5a.rep prn7h5a.tr prn7h5a.z prn7h5a.st (Magma.envs 7 2)
    ordprn7h5a_Law667 prn7h5a.hl prn7h5a.hr prn7h5aM481_endo prn7h5a.htr prn7h5a.hz prn7h5a.hst
    noprn7h5a_Law667

theorem Equation870_not_definableFrom_Equation481 :
    ¬ Law870.DefinableFrom Law481 :=
  not_definableFrom_transportSearch (prn7h5aM481 : Magma (Fin 7)) prn7h5aM481_models
    prn7h5a.E prn7h5a.Einv prn7h5a.rep prn7h5a.tr prn7h5a.z prn7h5a.st (Magma.envs 7 2)
    ordprn7h5a_Law870 prn7h5a.hl prn7h5a.hr prn7h5aM481_endo prn7h5a.htr prn7h5a.hz prn7h5a.hst
    noprn7h5a_Law870

theorem Equation917_not_definableFrom_Equation481 :
    ¬ Law917.DefinableFrom Law481 :=
  not_definableFrom_transportSearch (prn7h5aM481 : Magma (Fin 7)) prn7h5aM481_models
    prn7h5a.E prn7h5a.Einv prn7h5a.rep prn7h5a.tr prn7h5a.z prn7h5a.st (Magma.envs 7 2)
    ordprn7h5a_Law917 prn7h5a.hl prn7h5a.hr prn7h5aM481_endo prn7h5a.htr prn7h5a.hz prn7h5a.hst
    noprn7h5a_Law917

theorem Equation978_not_definableFrom_Equation481 :
    ¬ Law978.DefinableFrom Law481 :=
  not_definableFrom_transportSearch (prn7h5aM481 : Magma (Fin 7)) prn7h5aM481_models
    prn7h5a.E prn7h5a.Einv prn7h5a.rep prn7h5a.tr prn7h5a.z prn7h5a.st (Magma.envs 7 3)
    ordprn7h5a_Law978 prn7h5a.hl prn7h5a.hr prn7h5aM481_endo prn7h5a.htr prn7h5a.hz prn7h5a.hst
    noprn7h5a_Law978

theorem Equation1076_not_definableFrom_Equation1313 :
    ¬ Law1076.DefinableFrom Law1313 :=
  not_definableFrom_transportSearch (prn7h6aM1313 : Magma (Fin 7)) prn7h6aM1313_models
    prn7h6a.E prn7h6a.Einv prn7h6a.rep prn7h6a.tr prn7h6a.z prn7h6a.st (Magma.envs 7 2)
    ordprn7h6a_Law1076 prn7h6a.hl prn7h6a.hr prn7h6aM1313_endo prn7h6a.htr prn7h6a.hz prn7h6a.hst
    noprn7h6a_Law1076

theorem Equation66_not_definableFrom_Equation1083 :
    ¬ Law66.DefinableFrom Law1083 :=
  not_definableFrom_transportSearch (prn8h7aM1083 : Magma (Fin 8)) prn8h7aM1083_models
    prn8h7a.E prn8h7a.Einv prn8h7a.rep prn8h7a.tr prn8h7a.z prn8h7a.st (Magma.envs 8 2)
    ordprn8h7a_Law66 prn8h7a.hl prn8h7a.hr prn8h7aM1083_endo prn8h7a.htr prn8h7a.hz prn8h7a.hst
    noprn8h7a_Law66

theorem Equation1719_not_definableFrom_Equation1083 :
    ¬ Law1719.DefinableFrom Law1083 :=
  not_definableFrom_transportSearch (prn8h7aM1083 : Magma (Fin 8)) prn8h7aM1083_models
    prn8h7a.E prn8h7a.Einv prn8h7a.rep prn8h7a.tr prn8h7a.z prn8h7a.st (Magma.envs 8 2)
    ordprn8h7a_Law1719 prn8h7a.hl prn8h7a.hr prn8h7aM1083_endo prn8h7a.htr prn8h7a.hz prn8h7a.hst
    noprn8h7a_Law1719

theorem Equation313_not_definableFrom_Equation1480 :
    ¬ Law313.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law313 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law313

theorem Equation335_not_definableFrom_Equation1480 :
    ¬ Law335.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law335 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law335

theorem Equation1519_not_definableFrom_Equation1480 :
    ¬ Law1519.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law1519 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law1519

theorem Equation1682_not_definableFrom_Equation1480 :
    ¬ Law1682.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law1682 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law1682

theorem Equation3352_not_definableFrom_Equation1480 :
    ¬ Law3352.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law3352 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law3352

theorem Equation3472_not_definableFrom_Equation1480 :
    ¬ Law3472.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law3472 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law3472

theorem Equation3558_not_definableFrom_Equation1480 :
    ¬ Law3558.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law3558 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law3558

theorem Equation3588_not_definableFrom_Equation1480 :
    ¬ Law3588.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 3)
    ordprn8h8a_Law3588 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law3588

theorem Equation4273_not_definableFrom_Equation1480 :
    ¬ Law4273.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law4273 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law4273

theorem Equation4405_not_definableFrom_Equation1480 :
    ¬ Law4405.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (prn8h8aM1480 : Magma (Fin 8)) prn8h8aM1480_models
    prn8h8a.E prn8h8a.Einv prn8h8a.rep prn8h8a.tr prn8h8a.z prn8h8a.st (Magma.envs 8 2)
    ordprn8h8a_Law4405 prn8h8a.hl prn8h8a.hr prn8h8aM1480_endo prn8h8a.htr prn8h8a.hz prn8h8a.hst
    noprn8h8a_Law4405

theorem Equation3345_not_definableFrom_Equation1489 :
    ¬ Law3345.DefinableFrom Law1489 :=
  not_definableFrom_transportSearch (prn8h8cM1489 : Magma (Fin 8)) prn8h8cM1489_models
    prn8h8c.E prn8h8c.Einv prn8h8c.rep prn8h8c.tr prn8h8c.z prn8h8c.st (Magma.envs 8 2)
    ordprn8h8c_Law3345 prn8h8c.hl prn8h8c.hr prn8h8cM1489_endo prn8h8c.htr prn8h8c.hz prn8h8c.hst
    noprn8h8c_Law3345

theorem Equation3548_not_definableFrom_Equation1489 :
    ¬ Law3548.DefinableFrom Law1489 :=
  not_definableFrom_transportSearch (prn8h8cM1489 : Magma (Fin 8)) prn8h8cM1489_models
    prn8h8c.E prn8h8c.Einv prn8h8c.rep prn8h8c.tr prn8h8c.z prn8h8c.st (Magma.envs 8 2)
    ordprn8h8c_Law3548 prn8h8c.hl prn8h8c.hr prn8h8cM1489_endo prn8h8c.htr prn8h8c.hz prn8h8c.hst
    noprn8h8c_Law3548

theorem Equation335_not_definableFrom_Equation4415 :
    ¬ Law335.DefinableFrom Law4415 :=
  not_definableFrom_transportSearch (prn8h8bM4415 : Magma (Fin 8)) prn8h8bM4415_models
    prn8h8b.E prn8h8b.Einv prn8h8b.rep prn8h8b.tr prn8h8b.z prn8h8b.st (Magma.envs 8 2)
    ordprn8h8b_Law335 prn8h8b.hl prn8h8b.hr prn8h8bM4415_endo prn8h8b.htr prn8h8b.hz prn8h8b.hst
    noprn8h8b_Law335

theorem Equation3352_not_definableFrom_Equation4415 :
    ¬ Law3352.DefinableFrom Law4415 :=
  not_definableFrom_transportSearch (prn8h8bM4415 : Magma (Fin 8)) prn8h8bM4415_models
    prn8h8b.E prn8h8b.Einv prn8h8b.rep prn8h8b.tr prn8h8b.z prn8h8b.st (Magma.envs 8 2)
    ordprn8h8b_Law3352 prn8h8b.hl prn8h8b.hr prn8h8bM4415_endo prn8h8b.htr prn8h8b.hz prn8h8b.hst
    noprn8h8b_Law3352

theorem Equation3555_not_definableFrom_Equation4415 :
    ¬ Law3555.DefinableFrom Law4415 :=
  not_definableFrom_transportSearch (prn8h8bM4415 : Magma (Fin 8)) prn8h8bM4415_models
    prn8h8b.E prn8h8b.Einv prn8h8b.rep prn8h8b.tr prn8h8b.z prn8h8b.st (Magma.envs 8 2)
    ordprn8h8b_Law3555 prn8h8b.hl prn8h8b.hr prn8h8bM4415_endo prn8h8b.htr prn8h8b.hz prn8h8b.hst
    noprn8h8b_Law3555

theorem Equation3748_not_definableFrom_Equation4415 :
    ¬ Law3748.DefinableFrom Law4415 :=
  not_definableFrom_transportSearch (prn8h8bM4415 : Magma (Fin 8)) prn8h8bM4415_models
    prn8h8b.E prn8h8b.Einv prn8h8b.rep prn8h8b.tr prn8h8b.z prn8h8b.st (Magma.envs 8 2)
    ordprn8h8b_Law3748 prn8h8b.hl prn8h8b.hr prn8h8bM4415_endo prn8h8b.htr prn8h8b.hz prn8h8b.hst
    noprn8h8b_Law3748

