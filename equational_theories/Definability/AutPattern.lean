import equational_theories.Definability.Pat_pat36h720a
import equational_theories.Definability.Pat_pat36h720a_L14
import equational_theories.Definability.Pat_pat36h720a_L66
import equational_theories.Definability.Pat_pat36h720a_L115
import equational_theories.Definability.Pat_pat36h720a_L313
import equational_theories.Definability.Pat_pat36h720a_L335
import equational_theories.Definability.Pat_pat36h720a_L477
import equational_theories.Definability.Pat_pat36h720a_L501
import equational_theories.Definability.Pat_pat36h720a_L670
import equational_theories.Definability.Pat_pat36h720a_L680
import equational_theories.Definability.Pat_pat36h720a_L692
import equational_theories.Definability.Pat_pat36h720a_L707
import equational_theories.Definability.Pat_pat36h720a_L873
import equational_theories.Definability.Pat_pat36h720a_L880
import equational_theories.Definability.Pat_pat36h720a_L1113
import equational_theories.Definability.Pat_pat36h720a_L1117
import equational_theories.Definability.Pat_pat36h720a_L1276
import equational_theories.Definability.Pat_pat36h720a_L1316
import equational_theories.Definability.Pat_pat36h720a_L1492
import equational_theories.Definability.Pat_pat36h720a_L1695
import equational_theories.Definability.Pat_pat36h720a_L1719
import equational_theories.Definability.Pat_pat36h720a_L3352
import equational_theories.Definability.Pat_pat36h720a_L3558
import equational_theories.Definability.Pat_pat36h720a_L3588
import equational_theories.Definability.Pat_pat36h720a_L3620
import equational_theories.Definability.Pat_pat36h720a_L4273
import equational_theories.Definability.Pat_pat36h720a_L4290
import equational_theories.Definability.Pat_pat36h720a_L4369
import equational_theories.Definability.Pat_pat36h720a_L4408

/-!
# Refutations from the coordinate-shuffle frame

Every other symmetry refutation in this directory starts from a model somebody found and takes the
automorphism group it happens to have. This one chooses the group first. On `S^m` let

    (x_1..x_m) ◇ (y_1..y_m) = (z_1..z_m),      each `z_i` one of the `2m` input coordinates,

so that `Sym(S)` acting on every coordinate at once is a group of automorphisms whatever the choice
of shuffle. Equation 168, `x = (y ◇ x) ◇ (x ◇ z)`, *is* one of these: `(a, b) ◇ (c, d) = (b, c)` on
`S^2`. Its models therefore have square size -- it has none on `Fin 2, 3, 5, 6` and one on `Fin 4`
-- which is why no sweep over small carriers had ever produced a model of it, and why its row of
the board was untouched. Equations 167, 1480, 1483, 1485 and 1486 are the same magma.

The automorphism group is `Sym(6)` on `Fin 36`, of order 720, and its invariant family has
139,314,069,504 members. `Law.MagmaLaw.not_definableFrom_transportSearch` searches it rather than
walking it, and the trees close in a few thousand nodes.
-/

open Law Law.MagmaLaw

theorem Equation14_not_definableFrom_Equation168 :
    ¬ Law14.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law14
    ordpat36h720a_Law14 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law14

theorem Equation66_not_definableFrom_Equation168 :
    ¬ Law66.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law66
    ordpat36h720a_Law66 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law66

theorem Equation115_not_definableFrom_Equation168 :
    ¬ Law115.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law115
    ordpat36h720a_Law115 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law115

theorem Equation313_not_definableFrom_Equation168 :
    ¬ Law313.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law313
    ordpat36h720a_Law313 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law313

theorem Equation335_not_definableFrom_Equation168 :
    ¬ Law335.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law335
    ordpat36h720a_Law335 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law335

theorem Equation477_not_definableFrom_Equation168 :
    ¬ Law477.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law477
    ordpat36h720a_Law477 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law477

theorem Equation501_not_definableFrom_Equation168 :
    ¬ Law501.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law501
    ordpat36h720a_Law501 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law501

theorem Equation670_not_definableFrom_Equation168 :
    ¬ Law670.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law670
    ordpat36h720a_Law670 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law670

theorem Equation680_not_definableFrom_Equation168 :
    ¬ Law680.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law680
    ordpat36h720a_Law680 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law680

theorem Equation692_not_definableFrom_Equation168 :
    ¬ Law692.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law692
    ordpat36h720a_Law692 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law692

theorem Equation707_not_definableFrom_Equation168 :
    ¬ Law707.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law707
    ordpat36h720a_Law707 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law707

theorem Equation873_not_definableFrom_Equation168 :
    ¬ Law873.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law873
    ordpat36h720a_Law873 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law873

theorem Equation880_not_definableFrom_Equation168 :
    ¬ Law880.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law880
    ordpat36h720a_Law880 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law880

theorem Equation1113_not_definableFrom_Equation168 :
    ¬ Law1113.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1113
    ordpat36h720a_Law1113 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1113

theorem Equation1117_not_definableFrom_Equation168 :
    ¬ Law1117.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1117
    ordpat36h720a_Law1117 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1117

theorem Equation1276_not_definableFrom_Equation168 :
    ¬ Law1276.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1276
    ordpat36h720a_Law1276 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1276

theorem Equation1316_not_definableFrom_Equation168 :
    ¬ Law1316.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1316
    ordpat36h720a_Law1316 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1316

theorem Equation1492_not_definableFrom_Equation168 :
    ¬ Law1492.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1492
    ordpat36h720a_Law1492 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1492

theorem Equation1695_not_definableFrom_Equation168 :
    ¬ Law1695.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1695
    ordpat36h720a_Law1695 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1695

theorem Equation1719_not_definableFrom_Equation168 :
    ¬ Law1719.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1719
    ordpat36h720a_Law1719 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1719

theorem Equation3352_not_definableFrom_Equation168 :
    ¬ Law3352.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3352
    ordpat36h720a_Law3352 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3352

theorem Equation3558_not_definableFrom_Equation168 :
    ¬ Law3558.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3558
    ordpat36h720a_Law3558 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3558

theorem Equation3588_not_definableFrom_Equation168 :
    ¬ Law3588.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3588
    ordpat36h720a_Law3588 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3588

theorem Equation3620_not_definableFrom_Equation168 :
    ¬ Law3620.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3620
    ordpat36h720a_Law3620 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3620

theorem Equation4273_not_definableFrom_Equation168 :
    ¬ Law4273.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4273
    ordpat36h720a_Law4273 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4273

theorem Equation4290_not_definableFrom_Equation168 :
    ¬ Law4290.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4290
    ordpat36h720a_Law4290 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4290

theorem Equation4369_not_definableFrom_Equation168 :
    ¬ Law4369.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4369
    ordpat36h720a_Law4369 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4369

theorem Equation4408_not_definableFrom_Equation168 :
    ¬ Law4408.DefinableFrom Law168 :=
  not_definableFrom_transportSearch (pat36h720aM168 : Magma (Fin 36)) pat36h720aM168_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4408
    ordpat36h720a_Law4408 pat36h720a.hl pat36h720a.hr pat36h720aM168_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4408

theorem Equation4290_not_definableFrom_Equation1480 :
    ¬ Law4290.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (pat36h720aM1480 : Magma (Fin 36)) pat36h720aM1480_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4290
    ordpat36h720a_Law4290 pat36h720a.hl pat36h720a.hr pat36h720aM1480_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4290

theorem Equation4408_not_definableFrom_Equation1480 :
    ¬ Law4408.DefinableFrom Law1480 :=
  not_definableFrom_transportSearch (pat36h720aM1480 : Magma (Fin 36)) pat36h720aM1480_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4408
    ordpat36h720a_Law4408 pat36h720a.hl pat36h720a.hr pat36h720aM1480_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4408

theorem Equation14_not_definableFrom_Equation1483 :
    ¬ Law14.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law14
    ordpat36h720a_Law14 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law14

theorem Equation313_not_definableFrom_Equation1483 :
    ¬ Law313.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law313
    ordpat36h720a_Law313 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law313

theorem Equation335_not_definableFrom_Equation1483 :
    ¬ Law335.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law335
    ordpat36h720a_Law335 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law335

theorem Equation477_not_definableFrom_Equation1483 :
    ¬ Law477.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law477
    ordpat36h720a_Law477 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law477

theorem Equation680_not_definableFrom_Equation1483 :
    ¬ Law680.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law680
    ordpat36h720a_Law680 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law680

theorem Equation692_not_definableFrom_Equation1483 :
    ¬ Law692.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law692
    ordpat36h720a_Law692 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law692

theorem Equation707_not_definableFrom_Equation1483 :
    ¬ Law707.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law707
    ordpat36h720a_Law707 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law707

theorem Equation1113_not_definableFrom_Equation1483 :
    ¬ Law1113.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1113
    ordpat36h720a_Law1113 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1113

theorem Equation1117_not_definableFrom_Equation1483 :
    ¬ Law1117.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1117
    ordpat36h720a_Law1117 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1117

theorem Equation1276_not_definableFrom_Equation1483 :
    ¬ Law1276.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1276
    ordpat36h720a_Law1276 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1276

theorem Equation1316_not_definableFrom_Equation1483 :
    ¬ Law1316.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1316
    ordpat36h720a_Law1316 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1316

theorem Equation1492_not_definableFrom_Equation1483 :
    ¬ Law1492.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1492
    ordpat36h720a_Law1492 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1492

theorem Equation1695_not_definableFrom_Equation1483 :
    ¬ Law1695.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1695
    ordpat36h720a_Law1695 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1695

theorem Equation3352_not_definableFrom_Equation1483 :
    ¬ Law3352.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3352
    ordpat36h720a_Law3352 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3352

theorem Equation3558_not_definableFrom_Equation1483 :
    ¬ Law3558.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3558
    ordpat36h720a_Law3558 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3558

theorem Equation3588_not_definableFrom_Equation1483 :
    ¬ Law3588.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3588
    ordpat36h720a_Law3588 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3588

theorem Equation3620_not_definableFrom_Equation1483 :
    ¬ Law3620.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3620
    ordpat36h720a_Law3620 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3620

theorem Equation4273_not_definableFrom_Equation1483 :
    ¬ Law4273.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4273
    ordpat36h720a_Law4273 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4273

theorem Equation4290_not_definableFrom_Equation1483 :
    ¬ Law4290.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4290
    ordpat36h720a_Law4290 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4290

theorem Equation4369_not_definableFrom_Equation1483 :
    ¬ Law4369.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4369
    ordpat36h720a_Law4369 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4369

theorem Equation4408_not_definableFrom_Equation1483 :
    ¬ Law4408.DefinableFrom Law1483 :=
  not_definableFrom_transportSearch (pat36h720aM1483 : Magma (Fin 36)) pat36h720aM1483_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4408
    ordpat36h720a_Law4408 pat36h720a.hl pat36h720a.hr pat36h720aM1483_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4408

theorem Equation14_not_definableFrom_Equation1485 :
    ¬ Law14.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law14
    ordpat36h720a_Law14 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law14

theorem Equation313_not_definableFrom_Equation1485 :
    ¬ Law313.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law313
    ordpat36h720a_Law313 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law313

theorem Equation335_not_definableFrom_Equation1485 :
    ¬ Law335.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law335
    ordpat36h720a_Law335 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law335

theorem Equation477_not_definableFrom_Equation1485 :
    ¬ Law477.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law477
    ordpat36h720a_Law477 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law477

theorem Equation680_not_definableFrom_Equation1485 :
    ¬ Law680.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law680
    ordpat36h720a_Law680 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law680

theorem Equation692_not_definableFrom_Equation1485 :
    ¬ Law692.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law692
    ordpat36h720a_Law692 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law692

theorem Equation707_not_definableFrom_Equation1485 :
    ¬ Law707.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law707
    ordpat36h720a_Law707 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law707

theorem Equation1113_not_definableFrom_Equation1485 :
    ¬ Law1113.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1113
    ordpat36h720a_Law1113 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1113

theorem Equation1117_not_definableFrom_Equation1485 :
    ¬ Law1117.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1117
    ordpat36h720a_Law1117 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1117

theorem Equation1276_not_definableFrom_Equation1485 :
    ¬ Law1276.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1276
    ordpat36h720a_Law1276 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1276

theorem Equation1316_not_definableFrom_Equation1485 :
    ¬ Law1316.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1316
    ordpat36h720a_Law1316 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1316

theorem Equation1492_not_definableFrom_Equation1485 :
    ¬ Law1492.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1492
    ordpat36h720a_Law1492 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1492

theorem Equation1695_not_definableFrom_Equation1485 :
    ¬ Law1695.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1695
    ordpat36h720a_Law1695 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1695

theorem Equation3352_not_definableFrom_Equation1485 :
    ¬ Law3352.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3352
    ordpat36h720a_Law3352 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3352

theorem Equation3558_not_definableFrom_Equation1485 :
    ¬ Law3558.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3558
    ordpat36h720a_Law3558 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3558

theorem Equation3588_not_definableFrom_Equation1485 :
    ¬ Law3588.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3588
    ordpat36h720a_Law3588 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3588

theorem Equation3620_not_definableFrom_Equation1485 :
    ¬ Law3620.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3620
    ordpat36h720a_Law3620 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3620

theorem Equation4273_not_definableFrom_Equation1485 :
    ¬ Law4273.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4273
    ordpat36h720a_Law4273 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4273

theorem Equation4290_not_definableFrom_Equation1485 :
    ¬ Law4290.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4290
    ordpat36h720a_Law4290 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4290

theorem Equation4369_not_definableFrom_Equation1485 :
    ¬ Law4369.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4369
    ordpat36h720a_Law4369 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4369

theorem Equation4408_not_definableFrom_Equation1485 :
    ¬ Law4408.DefinableFrom Law1485 :=
  not_definableFrom_transportSearch (pat36h720aM1485 : Magma (Fin 36)) pat36h720aM1485_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4408
    ordpat36h720a_Law4408 pat36h720a.hl pat36h720a.hr pat36h720aM1485_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4408

theorem Equation14_not_definableFrom_Equation1486 :
    ¬ Law14.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law14
    ordpat36h720a_Law14 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law14

theorem Equation66_not_definableFrom_Equation1486 :
    ¬ Law66.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law66
    ordpat36h720a_Law66 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law66

theorem Equation115_not_definableFrom_Equation1486 :
    ¬ Law115.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law115
    ordpat36h720a_Law115 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law115

theorem Equation313_not_definableFrom_Equation1486 :
    ¬ Law313.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law313
    ordpat36h720a_Law313 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law313

theorem Equation335_not_definableFrom_Equation1486 :
    ¬ Law335.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law335
    ordpat36h720a_Law335 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law335

theorem Equation477_not_definableFrom_Equation1486 :
    ¬ Law477.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law477
    ordpat36h720a_Law477 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law477

theorem Equation501_not_definableFrom_Equation1486 :
    ¬ Law501.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law501
    ordpat36h720a_Law501 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law501

theorem Equation670_not_definableFrom_Equation1486 :
    ¬ Law670.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law670
    ordpat36h720a_Law670 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law670

theorem Equation680_not_definableFrom_Equation1486 :
    ¬ Law680.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law680
    ordpat36h720a_Law680 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law680

theorem Equation692_not_definableFrom_Equation1486 :
    ¬ Law692.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law692
    ordpat36h720a_Law692 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law692

theorem Equation707_not_definableFrom_Equation1486 :
    ¬ Law707.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law707
    ordpat36h720a_Law707 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law707

theorem Equation873_not_definableFrom_Equation1486 :
    ¬ Law873.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law873
    ordpat36h720a_Law873 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law873

theorem Equation880_not_definableFrom_Equation1486 :
    ¬ Law880.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law880
    ordpat36h720a_Law880 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law880

theorem Equation1113_not_definableFrom_Equation1486 :
    ¬ Law1113.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1113
    ordpat36h720a_Law1113 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1113

theorem Equation1117_not_definableFrom_Equation1486 :
    ¬ Law1117.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1117
    ordpat36h720a_Law1117 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1117

theorem Equation1276_not_definableFrom_Equation1486 :
    ¬ Law1276.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1276
    ordpat36h720a_Law1276 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1276

theorem Equation1316_not_definableFrom_Equation1486 :
    ¬ Law1316.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1316
    ordpat36h720a_Law1316 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1316

theorem Equation1492_not_definableFrom_Equation1486 :
    ¬ Law1492.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1492
    ordpat36h720a_Law1492 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1492

theorem Equation1695_not_definableFrom_Equation1486 :
    ¬ Law1695.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1695
    ordpat36h720a_Law1695 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1695

theorem Equation1719_not_definableFrom_Equation1486 :
    ¬ Law1719.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law1719
    ordpat36h720a_Law1719 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law1719

theorem Equation3352_not_definableFrom_Equation1486 :
    ¬ Law3352.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3352
    ordpat36h720a_Law3352 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3352

theorem Equation3558_not_definableFrom_Equation1486 :
    ¬ Law3558.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3558
    ordpat36h720a_Law3558 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3558

theorem Equation3588_not_definableFrom_Equation1486 :
    ¬ Law3588.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3588
    ordpat36h720a_Law3588 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3588

theorem Equation3620_not_definableFrom_Equation1486 :
    ¬ Law3620.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3620
    ordpat36h720a_Law3620 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3620

theorem Equation4273_not_definableFrom_Equation1486 :
    ¬ Law4273.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4273
    ordpat36h720a_Law4273 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4273

theorem Equation4290_not_definableFrom_Equation1486 :
    ¬ Law4290.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4290
    ordpat36h720a_Law4290 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4290

theorem Equation4369_not_definableFrom_Equation1486 :
    ¬ Law4369.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4369
    ordpat36h720a_Law4369 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4369

theorem Equation4408_not_definableFrom_Equation1486 :
    ¬ Law4408.DefinableFrom Law1486 :=
  not_definableFrom_transportSearch (pat36h720aM1486 : Magma (Fin 36)) pat36h720aM1486_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4408
    ordpat36h720a_Law4408 pat36h720a.hl pat36h720a.hr pat36h720aM1486_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4408

theorem Equation3588_not_definableFrom_Equation1519 :
    ¬ Law3588.DefinableFrom Law1519 :=
  not_definableFrom_transportSearch (pat36h720aM1519 : Magma (Fin 36)) pat36h720aM1519_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3588
    ordpat36h720a_Law3588 pat36h720a.hl pat36h720a.hr pat36h720aM1519_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3588

theorem Equation4273_not_definableFrom_Equation1519 :
    ¬ Law4273.DefinableFrom Law1519 :=
  not_definableFrom_transportSearch (pat36h720aM1519 : Magma (Fin 36)) pat36h720aM1519_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4273
    ordpat36h720a_Law4273 pat36h720a.hl pat36h720a.hr pat36h720aM1519_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4273

theorem Equation3588_not_definableFrom_Equation3472 :
    ¬ Law3588.DefinableFrom Law3472 :=
  not_definableFrom_transportSearch (pat36h720aM3472 : Magma (Fin 36)) pat36h720aM3472_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law3588
    ordpat36h720a_Law3588 pat36h720a.hl pat36h720a.hr pat36h720aM3472_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law3588

theorem Equation4273_not_definableFrom_Equation3472 :
    ¬ Law4273.DefinableFrom Law3472 :=
  not_definableFrom_transportSearch (pat36h720aM3472 : Magma (Fin 36)) pat36h720aM3472_models
    pat36h720a.E pat36h720a.Einv pat36h720a.rep pat36h720a.tr pat36h720a.z pat36h720a.st envpat36h720a_Law4273
    ordpat36h720a_Law4273 pat36h720a.hl pat36h720a.hr pat36h720aM3472_endo pat36h720a.htr pat36h720a.hz pat36h720a.hst
    nopat36h720a_Law4273

