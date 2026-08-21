import equational_theories.Definability.Aut_mau9h72a
import equational_theories.Definability.Aut_mau9h72a_L335
import equational_theories.Definability.Aut_mau9h72a_L1117
import equational_theories.Definability.Aut_mau9h72a_L3345
import equational_theories.Definability.Aut_mau9h72a_L3352
import equational_theories.Definability.Aut_mau9h72a_L3548
import equational_theories.Definability.Aut_mau9h72a_L3555
import equational_theories.Definability.Aut_mau9h72a_L3558
import equational_theories.Definability.Aut_mau9h72a_L3620
import equational_theories.Definability.Aut_mau9h72a_L3748
import equational_theories.Definability.Aut_mau9h72a_L4290
import equational_theories.Definability.Aut_mau9h72a_L4369
import equational_theories.Definability.Aut_mau9h72a_L4408
import equational_theories.Definability.Aut_mau11h110a
import equational_theories.Definability.Aut_mau11h110a_L167
import equational_theories.Definability.Aut_mau11h110a_L546
import equational_theories.Definability.Aut_mau11h110a_L1076
import equational_theories.Definability.Aut_mau11h110a_L1313
import equational_theories.Definability.Aut_mau11h110a_L1482
import equational_theories.Definability.Aut_mau11h110a_L1682
import equational_theories.Definability.Aut_mau11h110a_L3607
import equational_theories.Definability.Aut_mau11h110a_L3675
import equational_theories.Definability.Aut_mau11h110a_L4321
import equational_theories.Definability.Aut_mau11h110a_L4443
import equational_theories.Definability.Aut_mau13h156a
import equational_theories.Definability.Aut_mau13h156a_L63
import equational_theories.Definability.Aut_mau13h156a_L335
import equational_theories.Definability.Aut_mau13h156a_L464
import equational_theories.Definability.Aut_mau13h156a_L467
import equational_theories.Definability.Aut_mau13h156a_L474
import equational_theories.Definability.Aut_mau13h156a_L504
import equational_theories.Definability.Aut_mau13h156a_L546
import equational_theories.Definability.Aut_mau13h156a_L667
import equational_theories.Definability.Aut_mau13h156a_L677
import equational_theories.Definability.Aut_mau13h156a_L704
import equational_theories.Definability.Aut_mau13h156a_L870
import equational_theories.Definability.Aut_mau13h156a_L883
import equational_theories.Definability.Aut_mau13h156a_L917
import equational_theories.Definability.Aut_mau13h156a_L1110
import equational_theories.Definability.Aut_mau13h156a_L1117
import equational_theories.Definability.Aut_mau13h156a_L1279
import equational_theories.Definability.Aut_mau13h156a_L1489
import equational_theories.Definability.Aut_mau13h156a_L1516
import equational_theories.Definability.Aut_mau13h156a_L1685
import equational_theories.Definability.Aut_mau13h156a_L3269
import equational_theories.Definability.Aut_mau13h156a_L3279
import equational_theories.Definability.Aut_mau13h156a_L3345
import equational_theories.Definability.Aut_mau13h156a_L3352
import equational_theories.Definability.Aut_mau13h156a_L3475
import equational_theories.Definability.Aut_mau13h156a_L3482
import equational_theories.Definability.Aut_mau13h156a_L3548
import equational_theories.Definability.Aut_mau13h156a_L3558
import equational_theories.Definability.Aut_mau13h156a_L3607
import equational_theories.Definability.Aut_mau13h156a_L3748
import equational_theories.Definability.Aut_mau13h156a_L4290
import equational_theories.Definability.Aut_mau13h156a_L4293
import equational_theories.Definability.Aut_mau13h156a_L4369
import equational_theories.Definability.Aut_mau13h156a_L4408
import equational_theories.Definability.Aut_mau9h54a
import equational_theories.Definability.Aut_mau9h54a_L14
import equational_theories.Definability.Aut_mau9h54a_L66
import equational_theories.Definability.Aut_mau9h54a_L115
import equational_theories.Definability.Aut_mau9h54a_L313
import equational_theories.Definability.Aut_mau9h54a_L477
import equational_theories.Definability.Aut_mau9h54a_L492
import equational_theories.Definability.Aut_mau9h54a_L680
import equational_theories.Definability.Aut_mau9h54a_L692
import equational_theories.Definability.Aut_mau9h54a_L707
import equational_theories.Definability.Aut_mau9h54a_L873
import equational_theories.Definability.Aut_mau9h54a_L1113
import equational_theories.Definability.Aut_mau9h54a_L1276
import equational_theories.Definability.Aut_mau9h54a_L1519
import equational_theories.Definability.Aut_mau9h54a_L1719
import equational_theories.Definability.Aut_mau9h54a_L3272
import equational_theories.Definability.Aut_mau9h54a_L3364
import equational_theories.Definability.Aut_mau9h54a_L3472
import equational_theories.Definability.Aut_mau9h54a_L3588
import equational_theories.Definability.Aut_mau9h54a_L4273

/-!
# Refutations from the automorphism group of a banked model

`Definability/AutGroups.lean` sweeps the subgroups of `S_n` and searches each one's invariant
operations for both halves of the argument. That enumeration is what limits it to small carriers.
The files imported here invert the order: they start from a model of the source that was already
known, take its automorphism group, and ask whether any operation with that symmetry satisfies the
target.

The groups this produces are large -- order 156 on `Fin 13`, order 110 on `Fin 11` -- and that is
the point, because a large symmetry group leaves few invariant operations. On `Fin 13` there are
thirteen, so `Law.MagmaLaw.not_definableFrom_transportExact` searches thirteen candidates on a
carrier where the naive tuple space would have been hopeless.
-/

open Law Law.MagmaLaw

theorem Equation335_not_definableFrom_Equation167 :
    ¬ Law335.DefinableFrom Law167 :=
  not_definableFrom_transportExact (mau9h72aM167 : Magma (Fin 9)) mau9h72aM167_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM167_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law335

theorem Equation1117_not_definableFrom_Equation167 :
    ¬ Law1117.DefinableFrom Law167 :=
  not_definableFrom_transportExact (mau9h72aM167 : Magma (Fin 9)) mau9h72aM167_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM167_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law1117

theorem Equation3352_not_definableFrom_Equation167 :
    ¬ Law3352.DefinableFrom Law167 :=
  not_definableFrom_transportExact (mau9h72aM167 : Magma (Fin 9)) mau9h72aM167_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM167_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3352

theorem Equation3558_not_definableFrom_Equation167 :
    ¬ Law3558.DefinableFrom Law167 :=
  not_definableFrom_transportExact (mau9h72aM167 : Magma (Fin 9)) mau9h72aM167_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM167_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3558

theorem Equation3748_not_definableFrom_Equation167 :
    ¬ Law3748.DefinableFrom Law167 :=
  not_definableFrom_transportExact (mau9h72aM167 : Magma (Fin 9)) mau9h72aM167_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM167_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3748

theorem Equation4290_not_definableFrom_Equation167 :
    ¬ Law4290.DefinableFrom Law167 :=
  not_definableFrom_transportExact (mau9h72aM167 : Magma (Fin 9)) mau9h72aM167_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM167_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4290

theorem Equation4369_not_definableFrom_Equation167 :
    ¬ Law4369.DefinableFrom Law167 :=
  not_definableFrom_transportExact (mau9h72aM167 : Magma (Fin 9)) mau9h72aM167_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM167_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4369

theorem Equation4408_not_definableFrom_Equation167 :
    ¬ Law4408.DefinableFrom Law167 :=
  not_definableFrom_transportExact (mau9h72aM167 : Magma (Fin 9)) mau9h72aM167_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM167_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4408

theorem Equation335_not_definableFrom_Equation501 :
    ¬ Law335.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law335

theorem Equation1117_not_definableFrom_Equation501 :
    ¬ Law1117.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law1117

theorem Equation3352_not_definableFrom_Equation501 :
    ¬ Law3352.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3352

theorem Equation3558_not_definableFrom_Equation501 :
    ¬ Law3558.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3558

theorem Equation3620_not_definableFrom_Equation501 :
    ¬ Law3620.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3620

theorem Equation3748_not_definableFrom_Equation501 :
    ¬ Law3748.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3748

theorem Equation4290_not_definableFrom_Equation501 :
    ¬ Law4290.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4290

theorem Equation4369_not_definableFrom_Equation501 :
    ¬ Law4369.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4369

theorem Equation4408_not_definableFrom_Equation501 :
    ¬ Law4408.DefinableFrom Law501 :=
  not_definableFrom_transportExact (mau9h72aM501 : Magma (Fin 9)) mau9h72aM501_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM501_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4408

theorem Equation335_not_definableFrom_Equation1682 :
    ¬ Law335.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (mau9h72aM1682 : Magma (Fin 9)) mau9h72aM1682_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM1682_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law335

theorem Equation3352_not_definableFrom_Equation1682 :
    ¬ Law3352.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (mau9h72aM1682 : Magma (Fin 9)) mau9h72aM1682_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM1682_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3352

theorem Equation3558_not_definableFrom_Equation1682 :
    ¬ Law3558.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (mau9h72aM1682 : Magma (Fin 9)) mau9h72aM1682_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM1682_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3558

theorem Equation3748_not_definableFrom_Equation1682 :
    ¬ Law3748.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (mau9h72aM1682 : Magma (Fin 9)) mau9h72aM1682_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM1682_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3748

theorem Equation4290_not_definableFrom_Equation1682 :
    ¬ Law4290.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (mau9h72aM1682 : Magma (Fin 9)) mau9h72aM1682_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM1682_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4290

theorem Equation4369_not_definableFrom_Equation1682 :
    ¬ Law4369.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (mau9h72aM1682 : Magma (Fin 9)) mau9h72aM1682_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM1682_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4369

theorem Equation4408_not_definableFrom_Equation1682 :
    ¬ Law4408.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (mau9h72aM1682 : Magma (Fin 9)) mau9h72aM1682_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM1682_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4408

theorem Equation335_not_definableFrom_Equation3675 :
    ¬ Law335.DefinableFrom Law3675 :=
  not_definableFrom_transportExact (mau9h72aM3675 : Magma (Fin 9)) mau9h72aM3675_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM3675_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law335

theorem Equation3352_not_definableFrom_Equation3675 :
    ¬ Law3352.DefinableFrom Law3675 :=
  not_definableFrom_transportExact (mau9h72aM3675 : Magma (Fin 9)) mau9h72aM3675_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM3675_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3352

theorem Equation3558_not_definableFrom_Equation3675 :
    ¬ Law3558.DefinableFrom Law3675 :=
  not_definableFrom_transportExact (mau9h72aM3675 : Magma (Fin 9)) mau9h72aM3675_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM3675_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3558

theorem Equation3748_not_definableFrom_Equation3675 :
    ¬ Law3748.DefinableFrom Law3675 :=
  not_definableFrom_transportExact (mau9h72aM3675 : Magma (Fin 9)) mau9h72aM3675_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM3675_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3748

theorem Equation4290_not_definableFrom_Equation3675 :
    ¬ Law4290.DefinableFrom Law3675 :=
  not_definableFrom_transportExact (mau9h72aM3675 : Magma (Fin 9)) mau9h72aM3675_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM3675_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4290

theorem Equation4369_not_definableFrom_Equation3675 :
    ¬ Law4369.DefinableFrom Law3675 :=
  not_definableFrom_transportExact (mau9h72aM3675 : Magma (Fin 9)) mau9h72aM3675_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM3675_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4369

theorem Equation4408_not_definableFrom_Equation3675 :
    ¬ Law4408.DefinableFrom Law3675 :=
  not_definableFrom_transportExact (mau9h72aM3675 : Magma (Fin 9)) mau9h72aM3675_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM3675_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law4408

theorem Equation3345_not_definableFrom_Equation4293 :
    ¬ Law3345.DefinableFrom Law4293 :=
  not_definableFrom_transportExact (mau9h72aM4293 : Magma (Fin 9)) mau9h72aM4293_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM4293_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3345

theorem Equation3548_not_definableFrom_Equation4293 :
    ¬ Law3548.DefinableFrom Law4293 :=
  not_definableFrom_transportExact (mau9h72aM4293 : Magma (Fin 9)) mau9h72aM4293_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM4293_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3548

theorem Equation3555_not_definableFrom_Equation4293 :
    ¬ Law3555.DefinableFrom Law4293 :=
  not_definableFrom_transportExact (mau9h72aM4293 : Magma (Fin 9)) mau9h72aM4293_models
    mau9h72a.E mau9h72a.Einv mau9h72a.rep mau9h72a.tr mau9h72a.z mau9h72a.st
    mau9h72a.hl mau9h72a.hr mau9h72aM4293_endo mau9h72a.htr mau9h72a.hz mau9h72a.hst
    nomau9h72a_Law3555

theorem Equation1482_not_definableFrom_Equation670 :
    ¬ Law1482.DefinableFrom Law670 :=
  not_definableFrom_transportExact (mau11h110aM670 : Magma (Fin 11)) mau11h110aM670_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM670_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law1482

theorem Equation167_not_definableFrom_Equation677 :
    ¬ Law167.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law167

theorem Equation546_not_definableFrom_Equation677 :
    ¬ Law546.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law546

theorem Equation1076_not_definableFrom_Equation677 :
    ¬ Law1076.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law1076

theorem Equation1313_not_definableFrom_Equation677 :
    ¬ Law1313.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law1313

theorem Equation1482_not_definableFrom_Equation677 :
    ¬ Law1482.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law1482

theorem Equation1682_not_definableFrom_Equation677 :
    ¬ Law1682.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law1682

theorem Equation3607_not_definableFrom_Equation677 :
    ¬ Law3607.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law3607

theorem Equation3675_not_definableFrom_Equation677 :
    ¬ Law3675.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law3675

theorem Equation4321_not_definableFrom_Equation677 :
    ¬ Law4321.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law4321

theorem Equation4443_not_definableFrom_Equation677 :
    ¬ Law4443.DefinableFrom Law677 :=
  not_definableFrom_transportExact (mau11h110aM677 : Magma (Fin 11)) mau11h110aM677_models
    mau11h110a.E mau11h110a.Einv mau11h110a.rep mau11h110a.tr mau11h110a.z mau11h110a.st
    mau11h110a.hl mau11h110a.hr mau11h110aM677_endo mau11h110a.htr mau11h110a.hz mau11h110a.hst
    nomau11h110a_Law4443

theorem Equation63_not_definableFrom_Equation1076 :
    ¬ Law63.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law63

theorem Equation335_not_definableFrom_Equation1076 :
    ¬ Law335.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law335

theorem Equation464_not_definableFrom_Equation1076 :
    ¬ Law464.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law464

theorem Equation467_not_definableFrom_Equation1076 :
    ¬ Law467.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law467

theorem Equation474_not_definableFrom_Equation1076 :
    ¬ Law474.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law474

theorem Equation504_not_definableFrom_Equation1076 :
    ¬ Law504.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law504

theorem Equation546_not_definableFrom_Equation1076 :
    ¬ Law546.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law546

theorem Equation667_not_definableFrom_Equation1076 :
    ¬ Law667.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law667

theorem Equation677_not_definableFrom_Equation1076 :
    ¬ Law677.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law677

theorem Equation704_not_definableFrom_Equation1076 :
    ¬ Law704.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law704

theorem Equation870_not_definableFrom_Equation1076 :
    ¬ Law870.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law870

theorem Equation883_not_definableFrom_Equation1076 :
    ¬ Law883.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law883

theorem Equation917_not_definableFrom_Equation1076 :
    ¬ Law917.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law917

theorem Equation1110_not_definableFrom_Equation1076 :
    ¬ Law1110.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1110

theorem Equation1117_not_definableFrom_Equation1076 :
    ¬ Law1117.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1117

theorem Equation1279_not_definableFrom_Equation1076 :
    ¬ Law1279.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1279

theorem Equation1489_not_definableFrom_Equation1076 :
    ¬ Law1489.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1489

theorem Equation1516_not_definableFrom_Equation1076 :
    ¬ Law1516.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1516

theorem Equation1685_not_definableFrom_Equation1076 :
    ¬ Law1685.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1685

theorem Equation3269_not_definableFrom_Equation1076 :
    ¬ Law3269.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3269

theorem Equation3279_not_definableFrom_Equation1076 :
    ¬ Law3279.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3279

theorem Equation3345_not_definableFrom_Equation1076 :
    ¬ Law3345.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3345

theorem Equation3352_not_definableFrom_Equation1076 :
    ¬ Law3352.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3352

theorem Equation3475_not_definableFrom_Equation1076 :
    ¬ Law3475.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3475

theorem Equation3482_not_definableFrom_Equation1076 :
    ¬ Law3482.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3482

theorem Equation3548_not_definableFrom_Equation1076 :
    ¬ Law3548.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3548

theorem Equation3558_not_definableFrom_Equation1076 :
    ¬ Law3558.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3558

theorem Equation3607_not_definableFrom_Equation1076 :
    ¬ Law3607.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3607

theorem Equation3748_not_definableFrom_Equation1076 :
    ¬ Law3748.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3748

theorem Equation4290_not_definableFrom_Equation1076 :
    ¬ Law4290.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law4290

theorem Equation4369_not_definableFrom_Equation1076 :
    ¬ Law4369.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law4369

theorem Equation4408_not_definableFrom_Equation1076 :
    ¬ Law4408.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (mau13h156aM1076 : Magma (Fin 13)) mau13h156aM1076_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1076_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law4408

theorem Equation63_not_definableFrom_Equation1083 :
    ¬ Law63.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law63

theorem Equation504_not_definableFrom_Equation1083 :
    ¬ Law504.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law504

theorem Equation870_not_definableFrom_Equation1083 :
    ¬ Law870.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law870

theorem Equation917_not_definableFrom_Equation1083 :
    ¬ Law917.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law917

theorem Equation1685_not_definableFrom_Equation1083 :
    ¬ Law1685.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1685

theorem Equation3269_not_definableFrom_Equation1083 :
    ¬ Law3269.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3269

theorem Equation3279_not_definableFrom_Equation1083 :
    ¬ Law3279.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3279

theorem Equation3345_not_definableFrom_Equation1083 :
    ¬ Law3345.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3345

theorem Equation3475_not_definableFrom_Equation1083 :
    ¬ Law3475.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3475

theorem Equation3482_not_definableFrom_Equation1083 :
    ¬ Law3482.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3482

theorem Equation3548_not_definableFrom_Equation1083 :
    ¬ Law3548.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3548

theorem Equation4293_not_definableFrom_Equation1083 :
    ¬ Law4293.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (mau13h156aM1083 : Magma (Fin 13)) mau13h156aM1083_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1083_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law4293

theorem Equation63_not_definableFrom_Equation1286 :
    ¬ Law63.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law63

theorem Equation467_not_definableFrom_Equation1286 :
    ¬ Law467.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law467

theorem Equation504_not_definableFrom_Equation1286 :
    ¬ Law504.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law504

theorem Equation667_not_definableFrom_Equation1286 :
    ¬ Law667.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law667

theorem Equation704_not_definableFrom_Equation1286 :
    ¬ Law704.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law704

theorem Equation870_not_definableFrom_Equation1286 :
    ¬ Law870.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law870

theorem Equation883_not_definableFrom_Equation1286 :
    ¬ Law883.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law883

theorem Equation917_not_definableFrom_Equation1286 :
    ¬ Law917.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law917

theorem Equation1110_not_definableFrom_Equation1286 :
    ¬ Law1110.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1110

theorem Equation1279_not_definableFrom_Equation1286 :
    ¬ Law1279.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1279

theorem Equation1489_not_definableFrom_Equation1286 :
    ¬ Law1489.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1489

theorem Equation1516_not_definableFrom_Equation1286 :
    ¬ Law1516.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1516

theorem Equation1685_not_definableFrom_Equation1286 :
    ¬ Law1685.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law1685

theorem Equation3269_not_definableFrom_Equation1286 :
    ¬ Law3269.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3269

theorem Equation3279_not_definableFrom_Equation1286 :
    ¬ Law3279.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3279

theorem Equation3345_not_definableFrom_Equation1286 :
    ¬ Law3345.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3345

theorem Equation3475_not_definableFrom_Equation1286 :
    ¬ Law3475.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3475

theorem Equation3482_not_definableFrom_Equation1286 :
    ¬ Law3482.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3482

theorem Equation3548_not_definableFrom_Equation1286 :
    ¬ Law3548.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law3548

theorem Equation4293_not_definableFrom_Equation1286 :
    ¬ Law4293.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (mau13h156aM1286 : Magma (Fin 13)) mau13h156aM1286_models
    mau13h156a.E mau13h156a.Einv mau13h156a.rep mau13h156a.tr mau13h156a.z mau13h156a.st
    mau13h156a.hl mau13h156a.hr mau13h156aM1286_endo mau13h156a.htr mau13h156a.hz mau13h156a.hst
    nomau13h156a_Law4293

theorem Equation14_not_definableFrom_Equation907 :
    ¬ Law14.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law14

theorem Equation66_not_definableFrom_Equation907 :
    ¬ Law66.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law66

theorem Equation115_not_definableFrom_Equation907 :
    ¬ Law115.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law115

theorem Equation313_not_definableFrom_Equation907 :
    ¬ Law313.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law313

theorem Equation477_not_definableFrom_Equation907 :
    ¬ Law477.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law477

theorem Equation492_not_definableFrom_Equation907 :
    ¬ Law492.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law492

theorem Equation680_not_definableFrom_Equation907 :
    ¬ Law680.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law680

theorem Equation692_not_definableFrom_Equation907 :
    ¬ Law692.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law692

theorem Equation707_not_definableFrom_Equation907 :
    ¬ Law707.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law707

theorem Equation873_not_definableFrom_Equation907 :
    ¬ Law873.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law873

theorem Equation1113_not_definableFrom_Equation907 :
    ¬ Law1113.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law1113

theorem Equation1276_not_definableFrom_Equation907 :
    ¬ Law1276.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law1276

theorem Equation1519_not_definableFrom_Equation907 :
    ¬ Law1519.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law1519

theorem Equation1719_not_definableFrom_Equation907 :
    ¬ Law1719.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law1719

theorem Equation3272_not_definableFrom_Equation907 :
    ¬ Law3272.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law3272

theorem Equation3364_not_definableFrom_Equation907 :
    ¬ Law3364.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law3364

theorem Equation3472_not_definableFrom_Equation907 :
    ¬ Law3472.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law3472

theorem Equation3588_not_definableFrom_Equation907 :
    ¬ Law3588.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law3588

theorem Equation4273_not_definableFrom_Equation907 :
    ¬ Law4273.DefinableFrom Law907 :=
  not_definableFrom_transportExact (mau9h54aM907 : Magma (Fin 9)) mau9h54aM907_models
    mau9h54a.E mau9h54a.Einv mau9h54a.rep mau9h54a.tr mau9h54a.z mau9h54a.st
    mau9h54a.hl mau9h54a.hr mau9h54aM907_endo mau9h54a.htr mau9h54a.hz mau9h54a.hst
    nomau9h54a_Law4273

