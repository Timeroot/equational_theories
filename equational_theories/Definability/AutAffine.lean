import equational_theories.Definability.Aut_aff11h110a
import equational_theories.Definability.Aut_aff11h110a_L3675
import equational_theories.Definability.Aut_aff13h156a
import equational_theories.Definability.Aut_aff13h156a_L63
import equational_theories.Definability.Aut_aff13h156a_L335
import equational_theories.Definability.Aut_aff13h156a_L464
import equational_theories.Definability.Aut_aff13h156a_L467
import equational_theories.Definability.Aut_aff13h156a_L474
import equational_theories.Definability.Aut_aff13h156a_L504
import equational_theories.Definability.Aut_aff13h156a_L546
import equational_theories.Definability.Aut_aff13h156a_L667
import equational_theories.Definability.Aut_aff13h156a_L677
import equational_theories.Definability.Aut_aff13h156a_L704
import equational_theories.Definability.Aut_aff13h156a_L870
import equational_theories.Definability.Aut_aff13h156a_L883
import equational_theories.Definability.Aut_aff13h156a_L917
import equational_theories.Definability.Aut_aff13h156a_L1110
import equational_theories.Definability.Aut_aff13h156a_L1117
import equational_theories.Definability.Aut_aff13h156a_L1279
import equational_theories.Definability.Aut_aff13h156a_L1489
import equational_theories.Definability.Aut_aff13h156a_L1516
import equational_theories.Definability.Aut_aff13h156a_L1685
import equational_theories.Definability.Aut_aff13h156a_L3269
import equational_theories.Definability.Aut_aff13h156a_L3279
import equational_theories.Definability.Aut_aff13h156a_L3345
import equational_theories.Definability.Aut_aff13h156a_L3352
import equational_theories.Definability.Aut_aff13h156a_L3475
import equational_theories.Definability.Aut_aff13h156a_L3482
import equational_theories.Definability.Aut_aff13h156a_L3548
import equational_theories.Definability.Aut_aff13h156a_L3558
import equational_theories.Definability.Aut_aff13h156a_L3607
import equational_theories.Definability.Aut_aff13h156a_L3748
import equational_theories.Definability.Aut_aff13h156a_L4290
import equational_theories.Definability.Aut_aff13h156a_L4369
import equational_theories.Definability.Aut_aff13h156a_L4408
import equational_theories.Definability.Aut_aff17h272a
import equational_theories.Definability.Aut_aff17h272a_L707
import equational_theories.Definability.Aut_aff17h272a_L1113
import equational_theories.Definability.Aut_aff19h342a
import equational_theories.Definability.Aut_aff19h342a_L167
import equational_theories.Definability.Aut_aff19h342a_L1479
import equational_theories.Definability.Aut_aff19h342a_L1482
import equational_theories.Definability.Aut_aff19h342a_L1682
import equational_theories.Definability.Aut_aff19h342a_L3355
import equational_theories.Definability.Aut_aff19h342a_L3675
import equational_theories.Definability.Aut_aff19h342a_L4321
import equational_theories.Definability.Aut_aff19h342a_L4443
import equational_theories.Definability.Aut_aff31h930a
import equational_theories.Definability.Aut_aff31h930a_L63
import equational_theories.Definability.Aut_aff31h930a_L464
import equational_theories.Definability.Aut_aff31h930a_L467
import equational_theories.Definability.Aut_aff31h930a_L504
import equational_theories.Definability.Aut_aff31h930a_L667
import equational_theories.Definability.Aut_aff31h930a_L704
import equational_theories.Definability.Aut_aff31h930a_L870
import equational_theories.Definability.Aut_aff31h930a_L883
import equational_theories.Definability.Aut_aff31h930a_L917
import equational_theories.Definability.Aut_aff31h930a_L1110
import equational_theories.Definability.Aut_aff31h930a_L1279
import equational_theories.Definability.Aut_aff31h930a_L1489
import equational_theories.Definability.Aut_aff31h930a_L1516
import equational_theories.Definability.Aut_aff31h930a_L1685
import equational_theories.Definability.Aut_aff31h930a_L3269
import equational_theories.Definability.Aut_aff31h930a_L3279
import equational_theories.Definability.Aut_aff31h930a_L3345
import equational_theories.Definability.Aut_aff31h930a_L3475
import equational_theories.Definability.Aut_aff31h930a_L3482
import equational_theories.Definability.Aut_aff31h930a_L3548

/-!
# Refutations from the affine family over a prime field

The magma `x <> y = (1 - c) x + c y` on `ZMod p` is carried to itself by every map `x -> u x + v`:
the linear part comes out in front, and the translation part survives precisely because the two
coefficients sum to one. That is the whole of `AGL(1, p)`, a group of order `p (p - 1)` which acts
sharply 2-transitively, so it has two orbits on ordered pairs -- the diagonal and everything else --
and the operations invariant under it are exactly the `p` affine ones.

So the family is known in advance at every prime, without a model bank to look in, and it is small:
`Fin 31` costs 31 candidate operations, fewer than several of the `Fin 6` groups elsewhere in this
directory. A source law is usable when some `op_c` models it and a target is refuted when none
does, which is the same argument `Definability/Transport.lean` makes for every other symmetry
group here -- only the group is one nobody could have found by enumerating subgroups.
-/

open Law Law.MagmaLaw

theorem Equation3675_not_definableFrom_Equation474 :
    ¬ Law3675.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aff11h110aM474 : Magma (Fin 11)) aff11h110aM474_models
    aff11h110a.E aff11h110a.Einv aff11h110a.rep aff11h110a.tr aff11h110a.z aff11h110a.st
    aff11h110a.hl aff11h110a.hr aff11h110aM474_endo aff11h110a.htr aff11h110a.hz aff11h110a.hst
    noaff11h110a_Law3675

theorem Equation464_not_definableFrom_Equation907 :
    ¬ Law464.DefinableFrom Law907 :=
  not_definableFrom_transportExact (aff13h156aM907 : Magma (Fin 13)) aff13h156aM907_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM907_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law464

theorem Equation63_not_definableFrom_Equation1313 :
    ¬ Law63.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law63

theorem Equation335_not_definableFrom_Equation1313 :
    ¬ Law335.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law335

theorem Equation464_not_definableFrom_Equation1313 :
    ¬ Law464.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law464

theorem Equation467_not_definableFrom_Equation1313 :
    ¬ Law467.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law467

theorem Equation474_not_definableFrom_Equation1313 :
    ¬ Law474.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law474

theorem Equation504_not_definableFrom_Equation1313 :
    ¬ Law504.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law504

theorem Equation546_not_definableFrom_Equation1313 :
    ¬ Law546.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law546

theorem Equation667_not_definableFrom_Equation1313 :
    ¬ Law667.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law667

theorem Equation677_not_definableFrom_Equation1313 :
    ¬ Law677.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law677

theorem Equation704_not_definableFrom_Equation1313 :
    ¬ Law704.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law704

theorem Equation870_not_definableFrom_Equation1313 :
    ¬ Law870.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law870

theorem Equation883_not_definableFrom_Equation1313 :
    ¬ Law883.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law883

theorem Equation917_not_definableFrom_Equation1313 :
    ¬ Law917.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law917

theorem Equation1110_not_definableFrom_Equation1313 :
    ¬ Law1110.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law1110

theorem Equation1117_not_definableFrom_Equation1313 :
    ¬ Law1117.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law1117

theorem Equation1279_not_definableFrom_Equation1313 :
    ¬ Law1279.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law1279

theorem Equation1489_not_definableFrom_Equation1313 :
    ¬ Law1489.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law1489

theorem Equation1516_not_definableFrom_Equation1313 :
    ¬ Law1516.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law1516

theorem Equation1685_not_definableFrom_Equation1313 :
    ¬ Law1685.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law1685

theorem Equation3269_not_definableFrom_Equation1313 :
    ¬ Law3269.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3269

theorem Equation3279_not_definableFrom_Equation1313 :
    ¬ Law3279.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3279

theorem Equation3345_not_definableFrom_Equation1313 :
    ¬ Law3345.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3345

theorem Equation3352_not_definableFrom_Equation1313 :
    ¬ Law3352.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3352

theorem Equation3475_not_definableFrom_Equation1313 :
    ¬ Law3475.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3475

theorem Equation3482_not_definableFrom_Equation1313 :
    ¬ Law3482.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3482

theorem Equation3548_not_definableFrom_Equation1313 :
    ¬ Law3548.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3548

theorem Equation3558_not_definableFrom_Equation1313 :
    ¬ Law3558.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3558

theorem Equation3607_not_definableFrom_Equation1313 :
    ¬ Law3607.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3607

theorem Equation3748_not_definableFrom_Equation1313 :
    ¬ Law3748.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3748

theorem Equation4290_not_definableFrom_Equation1313 :
    ¬ Law4290.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law4290

theorem Equation4369_not_definableFrom_Equation1313 :
    ¬ Law4369.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law4369

theorem Equation4408_not_definableFrom_Equation1313 :
    ¬ Law4408.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff13h156aM1313 : Magma (Fin 13)) aff13h156aM1313_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM1313_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law4408

theorem Equation3345_not_definableFrom_Equation3555 :
    ¬ Law3345.DefinableFrom Law3555 :=
  not_definableFrom_transportExact (aff13h156aM3555 : Magma (Fin 13)) aff13h156aM3555_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM3555_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3345

theorem Equation3548_not_definableFrom_Equation3555 :
    ¬ Law3548.DefinableFrom Law3555 :=
  not_definableFrom_transportExact (aff13h156aM3555 : Magma (Fin 13)) aff13h156aM3555_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM3555_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3548

theorem Equation3352_not_definableFrom_Equation4321 :
    ¬ Law3352.DefinableFrom Law4321 :=
  not_definableFrom_transportExact (aff13h156aM4321 : Magma (Fin 13)) aff13h156aM4321_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM4321_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3352

theorem Equation3748_not_definableFrom_Equation4321 :
    ¬ Law3748.DefinableFrom Law4321 :=
  not_definableFrom_transportExact (aff13h156aM4321 : Magma (Fin 13)) aff13h156aM4321_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM4321_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3748

theorem Equation4408_not_definableFrom_Equation4321 :
    ¬ Law4408.DefinableFrom Law4321 :=
  not_definableFrom_transportExact (aff13h156aM4321 : Magma (Fin 13)) aff13h156aM4321_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM4321_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law4408

theorem Equation3558_not_definableFrom_Equation4443 :
    ¬ Law3558.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aff13h156aM4443 : Magma (Fin 13)) aff13h156aM4443_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM4443_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law3558

theorem Equation4290_not_definableFrom_Equation4443 :
    ¬ Law4290.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aff13h156aM4443 : Magma (Fin 13)) aff13h156aM4443_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM4443_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law4290

theorem Equation4408_not_definableFrom_Equation4443 :
    ¬ Law4408.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aff13h156aM4443 : Magma (Fin 13)) aff13h156aM4443_models
    aff13h156a.E aff13h156a.Einv aff13h156a.rep aff13h156a.tr aff13h156a.z aff13h156a.st
    aff13h156a.hl aff13h156a.hr aff13h156aM4443_endo aff13h156a.htr aff13h156a.hz aff13h156a.hst
    noaff13h156a_Law4408

theorem Equation1113_not_definableFrom_Equation167 :
    ¬ Law1113.DefinableFrom Law167 :=
  not_definableFrom_transportExact (aff17h272aM167 : Magma (Fin 17)) aff17h272aM167_models
    aff17h272a.E aff17h272a.Einv aff17h272a.rep aff17h272a.tr aff17h272a.z aff17h272a.st
    aff17h272a.hl aff17h272a.hr aff17h272aM167_endo aff17h272a.htr aff17h272a.hz aff17h272a.hst
    noaff17h272a_Law1113

theorem Equation707_not_definableFrom_Equation1076 :
    ¬ Law707.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (aff17h272aM1076 : Magma (Fin 17)) aff17h272aM1076_models
    aff17h272a.E aff17h272a.Einv aff17h272a.rep aff17h272a.tr aff17h272a.z aff17h272a.st
    aff17h272a.hl aff17h272a.hr aff17h272aM1076_endo aff17h272a.htr aff17h272a.hz aff17h272a.hst
    noaff17h272a_Law707

theorem Equation1113_not_definableFrom_Equation1076 :
    ¬ Law1113.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (aff17h272aM1076 : Magma (Fin 17)) aff17h272aM1076_models
    aff17h272a.E aff17h272a.Einv aff17h272a.rep aff17h272a.tr aff17h272a.z aff17h272a.st
    aff17h272a.hl aff17h272a.hr aff17h272aM1076_endo aff17h272a.htr aff17h272a.hz aff17h272a.hst
    noaff17h272a_Law1113

theorem Equation707_not_definableFrom_Equation1313 :
    ¬ Law707.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff17h272aM1313 : Magma (Fin 17)) aff17h272aM1313_models
    aff17h272a.E aff17h272a.Einv aff17h272a.rep aff17h272a.tr aff17h272a.z aff17h272a.st
    aff17h272a.hl aff17h272a.hr aff17h272aM1313_endo aff17h272a.htr aff17h272a.hz aff17h272a.hst
    noaff17h272a_Law707

theorem Equation1113_not_definableFrom_Equation1313 :
    ¬ Law1113.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff17h272aM1313 : Magma (Fin 17)) aff17h272aM1313_models
    aff17h272a.E aff17h272a.Einv aff17h272a.rep aff17h272a.tr aff17h272a.z aff17h272a.st
    aff17h272a.hl aff17h272a.hr aff17h272aM1313_endo aff17h272a.htr aff17h272a.hz aff17h272a.hst
    noaff17h272a_Law1113

theorem Equation1479_not_definableFrom_Equation670 :
    ¬ Law1479.DefinableFrom Law670 :=
  not_definableFrom_transportExact (aff19h342aM670 : Magma (Fin 19)) aff19h342aM670_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM670_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law1479

theorem Equation1479_not_definableFrom_Equation907 :
    ¬ Law1479.DefinableFrom Law907 :=
  not_definableFrom_transportExact (aff19h342aM907 : Magma (Fin 19)) aff19h342aM907_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM907_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law1479

theorem Equation3355_not_definableFrom_Equation907 :
    ¬ Law3355.DefinableFrom Law907 :=
  not_definableFrom_transportExact (aff19h342aM907 : Magma (Fin 19)) aff19h342aM907_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM907_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law3355

theorem Equation167_not_definableFrom_Equation1076 :
    ¬ Law167.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (aff19h342aM1076 : Magma (Fin 19)) aff19h342aM1076_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1076_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law167

theorem Equation1482_not_definableFrom_Equation1076 :
    ¬ Law1482.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (aff19h342aM1076 : Magma (Fin 19)) aff19h342aM1076_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1076_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law1482

theorem Equation1682_not_definableFrom_Equation1076 :
    ¬ Law1682.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (aff19h342aM1076 : Magma (Fin 19)) aff19h342aM1076_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1076_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law1682

theorem Equation3675_not_definableFrom_Equation1076 :
    ¬ Law3675.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (aff19h342aM1076 : Magma (Fin 19)) aff19h342aM1076_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1076_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law3675

theorem Equation4321_not_definableFrom_Equation1076 :
    ¬ Law4321.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (aff19h342aM1076 : Magma (Fin 19)) aff19h342aM1076_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1076_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law4321

theorem Equation4443_not_definableFrom_Equation1076 :
    ¬ Law4443.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (aff19h342aM1076 : Magma (Fin 19)) aff19h342aM1076_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1076_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law4443

theorem Equation167_not_definableFrom_Equation1313 :
    ¬ Law167.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff19h342aM1313 : Magma (Fin 19)) aff19h342aM1313_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1313_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law167

theorem Equation1482_not_definableFrom_Equation1313 :
    ¬ Law1482.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff19h342aM1313 : Magma (Fin 19)) aff19h342aM1313_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1313_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law1482

theorem Equation1682_not_definableFrom_Equation1313 :
    ¬ Law1682.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff19h342aM1313 : Magma (Fin 19)) aff19h342aM1313_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1313_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law1682

theorem Equation3675_not_definableFrom_Equation1313 :
    ¬ Law3675.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff19h342aM1313 : Magma (Fin 19)) aff19h342aM1313_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1313_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law3675

theorem Equation4321_not_definableFrom_Equation1313 :
    ¬ Law4321.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff19h342aM1313 : Magma (Fin 19)) aff19h342aM1313_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1313_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law4321

theorem Equation4443_not_definableFrom_Equation1313 :
    ¬ Law4443.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (aff19h342aM1313 : Magma (Fin 19)) aff19h342aM1313_models
    aff19h342a.E aff19h342a.Einv aff19h342a.rep aff19h342a.tr aff19h342a.z aff19h342a.st
    aff19h342a.hl aff19h342a.hr aff19h342aM1313_endo aff19h342a.htr aff19h342a.hz aff19h342a.hst
    noaff19h342a_Law4443

theorem Equation63_not_definableFrom_Equation677 :
    ¬ Law63.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law63

theorem Equation464_not_definableFrom_Equation677 :
    ¬ Law464.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law464

theorem Equation467_not_definableFrom_Equation677 :
    ¬ Law467.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law467

theorem Equation504_not_definableFrom_Equation677 :
    ¬ Law504.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law504

theorem Equation667_not_definableFrom_Equation677 :
    ¬ Law667.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law667

theorem Equation704_not_definableFrom_Equation677 :
    ¬ Law704.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law704

theorem Equation870_not_definableFrom_Equation677 :
    ¬ Law870.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law870

theorem Equation883_not_definableFrom_Equation677 :
    ¬ Law883.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law883

theorem Equation917_not_definableFrom_Equation677 :
    ¬ Law917.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law917

theorem Equation1110_not_definableFrom_Equation677 :
    ¬ Law1110.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law1110

theorem Equation1279_not_definableFrom_Equation677 :
    ¬ Law1279.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law1279

theorem Equation1489_not_definableFrom_Equation677 :
    ¬ Law1489.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law1489

theorem Equation1516_not_definableFrom_Equation677 :
    ¬ Law1516.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law1516

theorem Equation1685_not_definableFrom_Equation677 :
    ¬ Law1685.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law1685

theorem Equation3269_not_definableFrom_Equation677 :
    ¬ Law3269.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law3269

theorem Equation3279_not_definableFrom_Equation677 :
    ¬ Law3279.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law3279

theorem Equation3345_not_definableFrom_Equation677 :
    ¬ Law3345.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law3345

theorem Equation3475_not_definableFrom_Equation677 :
    ¬ Law3475.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law3475

theorem Equation3482_not_definableFrom_Equation677 :
    ¬ Law3482.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law3482

theorem Equation3548_not_definableFrom_Equation677 :
    ¬ Law3548.DefinableFrom Law677 :=
  not_definableFrom_transportExact (aff31h930aM677 : Magma (Fin 31)) aff31h930aM677_models
    aff31h930a.E aff31h930a.Einv aff31h930a.rep aff31h930a.tr aff31h930a.z aff31h930a.st
    aff31h930a.hl aff31h930a.hr aff31h930aM677_endo aff31h930a.htr aff31h930a.hz aff31h930a.hst
    noaff31h930a_Law3548

