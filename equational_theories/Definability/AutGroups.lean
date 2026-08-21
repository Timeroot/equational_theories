import equational_theories.Definability.Aut_aut5h8a
import equational_theories.Definability.Aut_aut5h8a_L63
import equational_theories.Definability.Aut_aut5h8a_L464
import equational_theories.Definability.Aut_aut5h8a_L707
import equational_theories.Definability.Aut_aut5h8a_L870
import equational_theories.Definability.Aut_aut5h8a_L917
import equational_theories.Definability.Aut_aut5h8a_L1113
import equational_theories.Definability.Aut_aut5h8a_L1117
import equational_theories.Definability.Aut_aut5h8a_L1482
import equational_theories.Definability.Aut_aut8h24a
import equational_theories.Definability.Aut_aut8h24a_L313
import equational_theories.Definability.Aut_aut8h24a_L1519
import equational_theories.Definability.Aut_aut8h24a_L3352
import equational_theories.Definability.Aut_aut8h24a_L3472
import equational_theories.Definability.Aut_aut8h24a_L3588
import equational_theories.Definability.Aut_aut8h24a_L4273
import equational_theories.Definability.Aut_aut8h24a_L4408
import equational_theories.Definability.Aut_aut5h4a
import equational_theories.Definability.Aut_aut5h4a_L66
import equational_theories.Definability.Aut_aut5h4a_L695
import equational_theories.Definability.Aut_aut5h4a_L1719
import equational_theories.Definability.Aut_aut6h6a
import equational_theories.Definability.Aut_aut6h6a_L335
import equational_theories.Definability.Aut_aut6h6a_L3558
import equational_theories.Definability.Aut_aut6h6a_L4290
import equational_theories.Definability.Aut_aut6h6a_L4443
import equational_theories.Definability.Aut_aut6h9a
import equational_theories.Definability.Aut_aut6h9a_L1479
import equational_theories.Definability.Aut_aut7h20a
import equational_theories.Definability.Aut_aut7h20a_L707
import equational_theories.Definability.Aut_aut7h20a_L1113
import equational_theories.Definability.Aut_aut6h6b
import equational_theories.Definability.Aut_aut6h6b_L43
import equational_theories.Definability.Aut_aut6h6b_L335
import equational_theories.Definability.Aut_aut6h6b_L3342
import equational_theories.Definability.Aut_aut6h6b_L3352
import equational_theories.Definability.Aut_aut6h6b_L3545
import equational_theories.Definability.Aut_aut6h6b_L3748
import equational_theories.Definability.Aut_aut6h6b_L4321
import equational_theories.Definability.Aut_aut6h6c
import equational_theories.Definability.Aut_aut6h6c_L4408

/-!
# Refutations from the enumerated symmetry groups

`Definability/AutTransport.lean` carries one file per group from a hand-written list.
`groupsweep.py` instead enumerates every subgroup of `S_n` and keeps those whose invariant
operations can be searched, which turns up groups nobody would have written down -- the order-eight
group on `Fin 5` below refutes eleven open cells on its own.

The argument is the same one, and `Definability/Transport.lean` still does all of it: a source is
usable when some invariant operation models it, a target is refuted when none does, and every pair
of the two is a cell.
-/

open Law Law.MagmaLaw

theorem Equation63_not_definableFrom_Equation474 :
    ¬ Law63.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aut5h8aM474 : Magma (Fin 5)) aut5h8aM474_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM474_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law63

theorem Equation464_not_definableFrom_Equation474 :
    ¬ Law464.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aut5h8aM474 : Magma (Fin 5)) aut5h8aM474_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM474_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law464

theorem Equation707_not_definableFrom_Equation474 :
    ¬ Law707.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aut5h8aM474 : Magma (Fin 5)) aut5h8aM474_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM474_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law707

theorem Equation870_not_definableFrom_Equation474 :
    ¬ Law870.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aut5h8aM474 : Magma (Fin 5)) aut5h8aM474_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM474_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law870

theorem Equation917_not_definableFrom_Equation474 :
    ¬ Law917.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aut5h8aM474 : Magma (Fin 5)) aut5h8aM474_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM474_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law917

theorem Equation1113_not_definableFrom_Equation474 :
    ¬ Law1113.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aut5h8aM474 : Magma (Fin 5)) aut5h8aM474_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM474_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law1113

theorem Equation1117_not_definableFrom_Equation474 :
    ¬ Law1117.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aut5h8aM474 : Magma (Fin 5)) aut5h8aM474_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM474_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law1117

theorem Equation1482_not_definableFrom_Equation474 :
    ¬ Law1482.DefinableFrom Law474 :=
  not_definableFrom_transportExact (aut5h8aM474 : Magma (Fin 5)) aut5h8aM474_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM474_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law1482

theorem Equation63_not_definableFrom_Equation1685 :
    ¬ Law63.DefinableFrom Law1685 :=
  not_definableFrom_transportExact (aut5h8aM1685 : Magma (Fin 5)) aut5h8aM1685_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM1685_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law63

theorem Equation870_not_definableFrom_Equation1685 :
    ¬ Law870.DefinableFrom Law1685 :=
  not_definableFrom_transportExact (aut5h8aM1685 : Magma (Fin 5)) aut5h8aM1685_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM1685_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law870

theorem Equation917_not_definableFrom_Equation1685 :
    ¬ Law917.DefinableFrom Law1685 :=
  not_definableFrom_transportExact (aut5h8aM1685 : Magma (Fin 5)) aut5h8aM1685_models
    aut5h8a.E aut5h8a.Einv aut5h8a.rep aut5h8a.tr aut5h8a.z aut5h8a.st
    aut5h8a.hl aut5h8a.hr aut5h8aM1685_endo aut5h8a.htr aut5h8a.hz aut5h8a.hst
    noaut5h8a_Law917

theorem Equation313_not_definableFrom_Equation3272 :
    ¬ Law313.DefinableFrom Law3272 :=
  not_definableFrom_transportExact (aut8h24aM3272 : Magma (Fin 8)) aut8h24aM3272_models
    aut8h24a.E aut8h24a.Einv aut8h24a.rep aut8h24a.tr aut8h24a.z aut8h24a.st
    aut8h24a.hl aut8h24a.hr aut8h24aM3272_endo aut8h24a.htr aut8h24a.hz aut8h24a.hst
    noaut8h24a_Law313

theorem Equation1519_not_definableFrom_Equation3272 :
    ¬ Law1519.DefinableFrom Law3272 :=
  not_definableFrom_transportExact (aut8h24aM3272 : Magma (Fin 8)) aut8h24aM3272_models
    aut8h24a.E aut8h24a.Einv aut8h24a.rep aut8h24a.tr aut8h24a.z aut8h24a.st
    aut8h24a.hl aut8h24a.hr aut8h24aM3272_endo aut8h24a.htr aut8h24a.hz aut8h24a.hst
    noaut8h24a_Law1519

theorem Equation3472_not_definableFrom_Equation3272 :
    ¬ Law3472.DefinableFrom Law3272 :=
  not_definableFrom_transportExact (aut8h24aM3272 : Magma (Fin 8)) aut8h24aM3272_models
    aut8h24a.E aut8h24a.Einv aut8h24a.rep aut8h24a.tr aut8h24a.z aut8h24a.st
    aut8h24a.hl aut8h24a.hr aut8h24aM3272_endo aut8h24a.htr aut8h24a.hz aut8h24a.hst
    noaut8h24a_Law3472

theorem Equation3588_not_definableFrom_Equation3272 :
    ¬ Law3588.DefinableFrom Law3272 :=
  not_definableFrom_transportExact (aut8h24aM3272 : Magma (Fin 8)) aut8h24aM3272_models
    aut8h24a.E aut8h24a.Einv aut8h24a.rep aut8h24a.tr aut8h24a.z aut8h24a.st
    aut8h24a.hl aut8h24a.hr aut8h24aM3272_endo aut8h24a.htr aut8h24a.hz aut8h24a.hst
    noaut8h24a_Law3588

theorem Equation4273_not_definableFrom_Equation3272 :
    ¬ Law4273.DefinableFrom Law3272 :=
  not_definableFrom_transportExact (aut8h24aM3272 : Magma (Fin 8)) aut8h24aM3272_models
    aut8h24a.E aut8h24a.Einv aut8h24a.rep aut8h24a.tr aut8h24a.z aut8h24a.st
    aut8h24a.hl aut8h24a.hr aut8h24aM3272_endo aut8h24a.htr aut8h24a.hz aut8h24a.hst
    noaut8h24a_Law4273

theorem Equation3352_not_definableFrom_Equation3748 :
    ¬ Law3352.DefinableFrom Law3748 :=
  not_definableFrom_transportExact (aut8h24aM3748 : Magma (Fin 8)) aut8h24aM3748_models
    aut8h24a.E aut8h24a.Einv aut8h24a.rep aut8h24a.tr aut8h24a.z aut8h24a.st
    aut8h24a.hl aut8h24a.hr aut8h24aM3748_endo aut8h24a.htr aut8h24a.hz aut8h24a.hst
    noaut8h24a_Law3352

theorem Equation4408_not_definableFrom_Equation3748 :
    ¬ Law4408.DefinableFrom Law3748 :=
  not_definableFrom_transportExact (aut8h24aM3748 : Magma (Fin 8)) aut8h24aM3748_models
    aut8h24a.E aut8h24a.Einv aut8h24a.rep aut8h24a.tr aut8h24a.z aut8h24a.st
    aut8h24a.hl aut8h24a.hr aut8h24aM3748_endo aut8h24a.htr aut8h24a.hz aut8h24a.hst
    noaut8h24a_Law4408

theorem Equation66_not_definableFrom_Equation115 :
    ¬ Law66.DefinableFrom Law115 :=
  not_definableFrom_transportExact (aut5h4aM115 : Magma (Fin 5)) aut5h4aM115_models
    aut5h4a.E aut5h4a.Einv aut5h4a.rep aut5h4a.tr aut5h4a.z aut5h4a.st
    aut5h4a.hl aut5h4a.hr aut5h4aM115_endo aut5h4a.htr aut5h4a.hz aut5h4a.hst
    noaut5h4a_Law66

theorem Equation1719_not_definableFrom_Equation115 :
    ¬ Law1719.DefinableFrom Law115 :=
  not_definableFrom_transportExact (aut5h4aM115 : Magma (Fin 5)) aut5h4aM115_models
    aut5h4a.E aut5h4a.Einv aut5h4a.rep aut5h4a.tr aut5h4a.z aut5h4a.st
    aut5h4a.hl aut5h4a.hr aut5h4aM115_endo aut5h4a.htr aut5h4a.hz aut5h4a.hst
    noaut5h4a_Law1719

theorem Equation695_not_definableFrom_Equation481 :
    ¬ Law695.DefinableFrom Law481 :=
  not_definableFrom_transportExact (aut5h4aM481 : Magma (Fin 5)) aut5h4aM481_models
    aut5h4a.E aut5h4a.Einv aut5h4a.rep aut5h4a.tr aut5h4a.z aut5h4a.st
    aut5h4a.hl aut5h4a.hr aut5h4aM481_endo aut5h4a.htr aut5h4a.hz aut5h4a.hst
    noaut5h4a_Law695

theorem Equation66_not_definableFrom_Equation501 :
    ¬ Law66.DefinableFrom Law501 :=
  not_definableFrom_transportExact (aut5h4aM501 : Magma (Fin 5)) aut5h4aM501_models
    aut5h4a.E aut5h4a.Einv aut5h4a.rep aut5h4a.tr aut5h4a.z aut5h4a.st
    aut5h4a.hl aut5h4a.hr aut5h4aM501_endo aut5h4a.htr aut5h4a.hz aut5h4a.hst
    noaut5h4a_Law66

theorem Equation1719_not_definableFrom_Equation501 :
    ¬ Law1719.DefinableFrom Law501 :=
  not_definableFrom_transportExact (aut5h4aM501 : Magma (Fin 5)) aut5h4aM501_models
    aut5h4a.E aut5h4a.Einv aut5h4a.rep aut5h4a.tr aut5h4a.z aut5h4a.st
    aut5h4a.hl aut5h4a.hr aut5h4aM501_endo aut5h4a.htr aut5h4a.hz aut5h4a.hst
    noaut5h4a_Law1719

theorem Equation66_not_definableFrom_Equation873 :
    ¬ Law66.DefinableFrom Law873 :=
  not_definableFrom_transportExact (aut5h4aM873 : Magma (Fin 5)) aut5h4aM873_models
    aut5h4a.E aut5h4a.Einv aut5h4a.rep aut5h4a.tr aut5h4a.z aut5h4a.st
    aut5h4a.hl aut5h4a.hr aut5h4aM873_endo aut5h4a.htr aut5h4a.hz aut5h4a.hst
    noaut5h4a_Law66

theorem Equation1719_not_definableFrom_Equation873 :
    ¬ Law1719.DefinableFrom Law873 :=
  not_definableFrom_transportExact (aut5h4aM873 : Magma (Fin 5)) aut5h4aM873_models
    aut5h4a.E aut5h4a.Einv aut5h4a.rep aut5h4a.tr aut5h4a.z aut5h4a.st
    aut5h4a.hl aut5h4a.hr aut5h4aM873_endo aut5h4a.htr aut5h4a.hz aut5h4a.hst
    noaut5h4a_Law1719

theorem Equation4290_not_definableFrom_Equation1482 :
    ¬ Law4290.DefinableFrom Law1482 :=
  not_definableFrom_transportExact (aut6h6aM1482 : Magma (Fin 6)) aut6h6aM1482_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM1482_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law4290

theorem Equation335_not_definableFrom_Equation3352 :
    ¬ Law335.DefinableFrom Law3352 :=
  not_definableFrom_transportExact (aut6h6aM3352 : Magma (Fin 6)) aut6h6aM3352_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM3352_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law335

theorem Equation3558_not_definableFrom_Equation3352 :
    ¬ Law3558.DefinableFrom Law3352 :=
  not_definableFrom_transportExact (aut6h6aM3352 : Magma (Fin 6)) aut6h6aM3352_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM3352_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law3558

theorem Equation4290_not_definableFrom_Equation3352 :
    ¬ Law4290.DefinableFrom Law3352 :=
  not_definableFrom_transportExact (aut6h6aM3352 : Magma (Fin 6)) aut6h6aM3352_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM3352_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law4290

theorem Equation335_not_definableFrom_Equation3748 :
    ¬ Law335.DefinableFrom Law3748 :=
  not_definableFrom_transportExact (aut6h6aM3748 : Magma (Fin 6)) aut6h6aM3748_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM3748_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law335

theorem Equation3558_not_definableFrom_Equation3748 :
    ¬ Law3558.DefinableFrom Law3748 :=
  not_definableFrom_transportExact (aut6h6aM3748 : Magma (Fin 6)) aut6h6aM3748_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM3748_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law3558

theorem Equation4290_not_definableFrom_Equation3748 :
    ¬ Law4290.DefinableFrom Law3748 :=
  not_definableFrom_transportExact (aut6h6aM3748 : Magma (Fin 6)) aut6h6aM3748_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM3748_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law4290

theorem Equation335_not_definableFrom_Equation4321 :
    ¬ Law335.DefinableFrom Law4321 :=
  not_definableFrom_transportExact (aut6h6aM4321 : Magma (Fin 6)) aut6h6aM4321_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM4321_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law335

theorem Equation3558_not_definableFrom_Equation4321 :
    ¬ Law3558.DefinableFrom Law4321 :=
  not_definableFrom_transportExact (aut6h6aM4321 : Magma (Fin 6)) aut6h6aM4321_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM4321_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law3558

theorem Equation4290_not_definableFrom_Equation4321 :
    ¬ Law4290.DefinableFrom Law4321 :=
  not_definableFrom_transportExact (aut6h6aM4321 : Magma (Fin 6)) aut6h6aM4321_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM4321_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law4290

theorem Equation4443_not_definableFrom_Equation4321 :
    ¬ Law4443.DefinableFrom Law4321 :=
  not_definableFrom_transportExact (aut6h6aM4321 : Magma (Fin 6)) aut6h6aM4321_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM4321_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law4443

theorem Equation4290_not_definableFrom_Equation4408 :
    ¬ Law4290.DefinableFrom Law4408 :=
  not_definableFrom_transportExact (aut6h6aM4408 : Magma (Fin 6)) aut6h6aM4408_models
    aut6h6a.E aut6h6a.Einv aut6h6a.rep aut6h6a.tr aut6h6a.z aut6h6a.st
    aut6h6a.hl aut6h6a.hr aut6h6aM4408_endo aut6h6a.htr aut6h6a.hz aut6h6a.hst
    noaut6h6a_Law4290

theorem Equation1479_not_definableFrom_Equation3355 :
    ¬ Law1479.DefinableFrom Law3355 :=
  not_definableFrom_transportExact (aut6h9aM3355 : Magma (Fin 6)) aut6h9aM3355_models
    aut6h9a.E aut6h9a.Einv aut6h9a.rep aut6h9a.tr aut6h9a.z aut6h9a.st
    aut6h9a.hl aut6h9a.hr aut6h9aM3355_endo aut6h9a.htr aut6h9a.hz aut6h9a.hst
    noaut6h9a_Law1479

theorem Equation707_not_definableFrom_Equation1682 :
    ¬ Law707.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (aut7h20aM1682 : Magma (Fin 7)) aut7h20aM1682_models
    aut7h20a.E aut7h20a.Einv aut7h20a.rep aut7h20a.tr aut7h20a.z aut7h20a.st
    aut7h20a.hl aut7h20a.hr aut7h20aM1682_endo aut7h20a.htr aut7h20a.hz aut7h20a.hst
    noaut7h20a_Law707

theorem Equation1113_not_definableFrom_Equation1682 :
    ¬ Law1113.DefinableFrom Law1682 :=
  not_definableFrom_transportExact (aut7h20aM1682 : Magma (Fin 7)) aut7h20aM1682_models
    aut7h20a.E aut7h20a.Einv aut7h20a.rep aut7h20a.tr aut7h20a.z aut7h20a.st
    aut7h20a.hl aut7h20a.hr aut7h20aM1682_endo aut7h20a.htr aut7h20a.hz aut7h20a.hst
    noaut7h20a_Law1113

theorem Equation335_not_definableFrom_Equation3558 :
    ¬ Law335.DefinableFrom Law3558 :=
  not_definableFrom_transportExact (aut6h6bM3558 : Magma (Fin 6)) aut6h6bM3558_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM3558_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law335

theorem Equation3352_not_definableFrom_Equation3558 :
    ¬ Law3352.DefinableFrom Law3558 :=
  not_definableFrom_transportExact (aut6h6bM3558 : Magma (Fin 6)) aut6h6bM3558_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM3558_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law3352

theorem Equation3748_not_definableFrom_Equation3558 :
    ¬ Law3748.DefinableFrom Law3558 :=
  not_definableFrom_transportExact (aut6h6bM3558 : Magma (Fin 6)) aut6h6bM3558_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM3558_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law3748

theorem Equation3342_not_definableFrom_Equation4405 :
    ¬ Law3342.DefinableFrom Law4405 :=
  not_definableFrom_transportExact (aut6h6bM4405 : Magma (Fin 6)) aut6h6bM4405_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4405_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law3342

theorem Equation3545_not_definableFrom_Equation4405 :
    ¬ Law3545.DefinableFrom Law4405 :=
  not_definableFrom_transportExact (aut6h6bM4405 : Magma (Fin 6)) aut6h6bM4405_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4405_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law3545

theorem Equation43_not_definableFrom_Equation4443 :
    ¬ Law43.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aut6h6bM4443 : Magma (Fin 6)) aut6h6bM4443_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4443_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law43

theorem Equation335_not_definableFrom_Equation4443 :
    ¬ Law335.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aut6h6bM4443 : Magma (Fin 6)) aut6h6bM4443_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4443_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law335

theorem Equation3342_not_definableFrom_Equation4443 :
    ¬ Law3342.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aut6h6bM4443 : Magma (Fin 6)) aut6h6bM4443_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4443_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law3342

theorem Equation3352_not_definableFrom_Equation4443 :
    ¬ Law3352.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aut6h6bM4443 : Magma (Fin 6)) aut6h6bM4443_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4443_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law3352

theorem Equation3545_not_definableFrom_Equation4443 :
    ¬ Law3545.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aut6h6bM4443 : Magma (Fin 6)) aut6h6bM4443_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4443_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law3545

theorem Equation3748_not_definableFrom_Equation4443 :
    ¬ Law3748.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aut6h6bM4443 : Magma (Fin 6)) aut6h6bM4443_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4443_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law3748

theorem Equation4321_not_definableFrom_Equation4443 :
    ¬ Law4321.DefinableFrom Law4443 :=
  not_definableFrom_transportExact (aut6h6bM4443 : Magma (Fin 6)) aut6h6bM4443_models
    aut6h6b.E aut6h6b.Einv aut6h6b.rep aut6h6b.tr aut6h6b.z aut6h6b.st
    aut6h6b.hl aut6h6b.hr aut6h6bM4443_endo aut6h6b.htr aut6h6b.hz aut6h6b.hst
    noaut6h6b_Law4321

theorem Equation4408_not_definableFrom_Equation1482 :
    ¬ Law4408.DefinableFrom Law1482 :=
  not_definableFrom_transportExact (aut6h6cM1482 : Magma (Fin 6)) aut6h6cM1482_models
    aut6h6c.E aut6h6c.Einv aut6h6c.rep aut6h6c.tr aut6h6c.z aut6h6c.st
    aut6h6c.hl aut6h6c.hr aut6h6cM1482_endo aut6h6c.htr aut6h6c.hz aut6h6c.hst
    noaut6h6c_Law4408

theorem Equation4408_not_definableFrom_Equation4290 :
    ¬ Law4408.DefinableFrom Law4290 :=
  not_definableFrom_transportExact (aut6h6cM4290 : Magma (Fin 6)) aut6h6cM4290_models
    aut6h6c.E aut6h6c.Einv aut6h6c.rep aut6h6c.tr aut6h6c.z aut6h6c.st
    aut6h6c.hl aut6h6c.hr aut6h6cM4290_endo aut6h6c.htr aut6h6c.hz aut6h6c.hst
    noaut6h6c_Law4408

