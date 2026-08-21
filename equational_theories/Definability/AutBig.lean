import equational_theories.Definability.Aut_big16h240a
import equational_theories.Definability.Aut_big16h240a_L43
import equational_theories.Definability.Aut_big16h240a_L3342
import equational_theories.Definability.Aut_big16h240a_L3545
import equational_theories.Definability.Aut_big16h240a_L4405
import equational_theories.Definability.Aut_big29h406a
import equational_theories.Definability.Aut_big29h406a_L474
import equational_theories.Definability.Aut_big47h1081a
import equational_theories.Definability.Aut_big47h1081a_L504
import equational_theories.Definability.Aut_big47h1081a_L3269
import equational_theories.Definability.Aut_big47h1081a_L3279
import equational_theories.Definability.Aut_big47h1081a_L3475
import equational_theories.Definability.Aut_big47h1081a_L3482
import equational_theories.Definability.Aut_big59h1711a
import equational_theories.Definability.Aut_big59h1711a_L14
import equational_theories.Definability.Aut_big59h1711a_L66
import equational_theories.Definability.Aut_big59h1711a_L115
import equational_theories.Definability.Aut_big59h1711a_L313
import equational_theories.Definability.Aut_big59h1711a_L477
import equational_theories.Definability.Aut_big59h1711a_L680
import equational_theories.Definability.Aut_big59h1711a_L873
import equational_theories.Definability.Aut_big59h1711a_L1083
import equational_theories.Definability.Aut_big59h1711a_L1276
import equational_theories.Definability.Aut_big59h1711a_L1519
import equational_theories.Definability.Aut_big59h1711a_L1719
import equational_theories.Definability.Aut_big59h1711a_L3272
import equational_theories.Definability.Aut_big59h1711a_L3472
import equational_theories.Definability.Aut_big59h1711a_L4273

/-!
# Refutations from the affine groups over a finite field

`Definability/AutAffine.lean` takes the whole of `AGL(1, p)` over a prime field. The same argument
runs over any finite field and over `ZMod m`, and it runs over a subgroup of the units as well: for
`G_H = {x ↦ u x + v : u ∈ H}` the orbits on ordered pairs are the diagonal together with one per
coset of `H` among the nonzero differences, so the invariant family has `q ^ k` members with `k` the
index of `H`. A smaller group is a larger family, which models more sources and refutes fewer
targets; the sweep takes whichever end of that trade closes a cell.

What actually pays here is `F_16`. Characteristic two is not reachable at all from a prime field,
and sixteen is small enough that the family is still sixteen operations.
-/

open Law Law.MagmaLaw

theorem Equation43_not_definableFrom_Equation464 :
    ¬ Law43.DefinableFrom Law464 :=
  not_definableFrom_transportExact (big16h240aM464 : Magma (Fin 16)) big16h240aM464_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM464_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law43

theorem Equation3342_not_definableFrom_Equation464 :
    ¬ Law3342.DefinableFrom Law464 :=
  not_definableFrom_transportExact (big16h240aM464 : Magma (Fin 16)) big16h240aM464_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM464_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3342

theorem Equation3545_not_definableFrom_Equation464 :
    ¬ Law3545.DefinableFrom Law464 :=
  not_definableFrom_transportExact (big16h240aM464 : Magma (Fin 16)) big16h240aM464_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM464_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3545

theorem Equation4405_not_definableFrom_Equation464 :
    ¬ Law4405.DefinableFrom Law464 :=
  not_definableFrom_transportExact (big16h240aM464 : Magma (Fin 16)) big16h240aM464_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM464_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law4405

theorem Equation43_not_definableFrom_Equation474 :
    ¬ Law43.DefinableFrom Law474 :=
  not_definableFrom_transportExact (big16h240aM474 : Magma (Fin 16)) big16h240aM474_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM474_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law43

theorem Equation3342_not_definableFrom_Equation474 :
    ¬ Law3342.DefinableFrom Law474 :=
  not_definableFrom_transportExact (big16h240aM474 : Magma (Fin 16)) big16h240aM474_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM474_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3342

theorem Equation3545_not_definableFrom_Equation474 :
    ¬ Law3545.DefinableFrom Law474 :=
  not_definableFrom_transportExact (big16h240aM474 : Magma (Fin 16)) big16h240aM474_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM474_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3545

theorem Equation4405_not_definableFrom_Equation474 :
    ¬ Law4405.DefinableFrom Law474 :=
  not_definableFrom_transportExact (big16h240aM474 : Magma (Fin 16)) big16h240aM474_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM474_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law4405

theorem Equation43_not_definableFrom_Equation677 :
    ¬ Law43.DefinableFrom Law677 :=
  not_definableFrom_transportExact (big16h240aM677 : Magma (Fin 16)) big16h240aM677_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM677_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law43

theorem Equation3342_not_definableFrom_Equation677 :
    ¬ Law3342.DefinableFrom Law677 :=
  not_definableFrom_transportExact (big16h240aM677 : Magma (Fin 16)) big16h240aM677_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM677_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3342

theorem Equation3545_not_definableFrom_Equation677 :
    ¬ Law3545.DefinableFrom Law677 :=
  not_definableFrom_transportExact (big16h240aM677 : Magma (Fin 16)) big16h240aM677_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM677_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3545

theorem Equation4405_not_definableFrom_Equation677 :
    ¬ Law4405.DefinableFrom Law677 :=
  not_definableFrom_transportExact (big16h240aM677 : Magma (Fin 16)) big16h240aM677_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM677_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law4405

theorem Equation43_not_definableFrom_Equation1076 :
    ¬ Law43.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (big16h240aM1076 : Magma (Fin 16)) big16h240aM1076_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1076_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law43

theorem Equation3342_not_definableFrom_Equation1076 :
    ¬ Law3342.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (big16h240aM1076 : Magma (Fin 16)) big16h240aM1076_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1076_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3342

theorem Equation3545_not_definableFrom_Equation1076 :
    ¬ Law3545.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (big16h240aM1076 : Magma (Fin 16)) big16h240aM1076_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1076_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3545

theorem Equation4405_not_definableFrom_Equation1076 :
    ¬ Law4405.DefinableFrom Law1076 :=
  not_definableFrom_transportExact (big16h240aM1076 : Magma (Fin 16)) big16h240aM1076_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1076_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law4405

theorem Equation43_not_definableFrom_Equation1083 :
    ¬ Law43.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (big16h240aM1083 : Magma (Fin 16)) big16h240aM1083_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1083_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law43

theorem Equation3342_not_definableFrom_Equation1083 :
    ¬ Law3342.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (big16h240aM1083 : Magma (Fin 16)) big16h240aM1083_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1083_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3342

theorem Equation3545_not_definableFrom_Equation1083 :
    ¬ Law3545.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (big16h240aM1083 : Magma (Fin 16)) big16h240aM1083_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1083_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3545

theorem Equation4405_not_definableFrom_Equation1083 :
    ¬ Law4405.DefinableFrom Law1083 :=
  not_definableFrom_transportExact (big16h240aM1083 : Magma (Fin 16)) big16h240aM1083_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1083_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law4405

theorem Equation43_not_definableFrom_Equation1286 :
    ¬ Law43.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big16h240aM1286 : Magma (Fin 16)) big16h240aM1286_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1286_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law43

theorem Equation3342_not_definableFrom_Equation1286 :
    ¬ Law3342.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big16h240aM1286 : Magma (Fin 16)) big16h240aM1286_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1286_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3342

theorem Equation3545_not_definableFrom_Equation1286 :
    ¬ Law3545.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big16h240aM1286 : Magma (Fin 16)) big16h240aM1286_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1286_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3545

theorem Equation4405_not_definableFrom_Equation1286 :
    ¬ Law4405.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big16h240aM1286 : Magma (Fin 16)) big16h240aM1286_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1286_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law4405

theorem Equation43_not_definableFrom_Equation1313 :
    ¬ Law43.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (big16h240aM1313 : Magma (Fin 16)) big16h240aM1313_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1313_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law43

theorem Equation3342_not_definableFrom_Equation1313 :
    ¬ Law3342.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (big16h240aM1313 : Magma (Fin 16)) big16h240aM1313_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1313_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3342

theorem Equation3545_not_definableFrom_Equation1313 :
    ¬ Law3545.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (big16h240aM1313 : Magma (Fin 16)) big16h240aM1313_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1313_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law3545

theorem Equation4405_not_definableFrom_Equation1313 :
    ¬ Law4405.DefinableFrom Law1313 :=
  not_definableFrom_transportExact (big16h240aM1313 : Magma (Fin 16)) big16h240aM1313_models
    big16h240a.E big16h240a.Einv big16h240a.rep big16h240a.tr big16h240a.z big16h240a.st
    big16h240a.hl big16h240a.hr big16h240aM1313_endo big16h240a.htr big16h240a.hz big16h240a.hst
    nobig16h240a_Law4405

theorem Equation474_not_definableFrom_Equation677 :
    ¬ Law474.DefinableFrom Law677 :=
  not_definableFrom_transportExact (big29h406aM677 : Magma (Fin 29)) big29h406aM677_models
    big29h406a.E big29h406a.Einv big29h406a.rep big29h406a.tr big29h406a.z big29h406a.st
    big29h406a.hl big29h406a.hr big29h406aM677_endo big29h406a.htr big29h406a.hz big29h406a.hst
    nobig29h406a_Law474

theorem Equation504_not_definableFrom_Equation1685 :
    ¬ Law504.DefinableFrom Law1685 :=
  not_definableFrom_transportExact (big47h1081aM1685 : Magma (Fin 47)) big47h1081aM1685_models
    big47h1081a.E big47h1081a.Einv big47h1081a.rep big47h1081a.tr big47h1081a.z big47h1081a.st
    big47h1081a.hl big47h1081a.hr big47h1081aM1685_endo big47h1081a.htr big47h1081a.hz big47h1081a.hst
    nobig47h1081a_Law504

theorem Equation3269_not_definableFrom_Equation1685 :
    ¬ Law3269.DefinableFrom Law1685 :=
  not_definableFrom_transportExact (big47h1081aM1685 : Magma (Fin 47)) big47h1081aM1685_models
    big47h1081a.E big47h1081a.Einv big47h1081a.rep big47h1081a.tr big47h1081a.z big47h1081a.st
    big47h1081a.hl big47h1081a.hr big47h1081aM1685_endo big47h1081a.htr big47h1081a.hz big47h1081a.hst
    nobig47h1081a_Law3269

theorem Equation3279_not_definableFrom_Equation1685 :
    ¬ Law3279.DefinableFrom Law1685 :=
  not_definableFrom_transportExact (big47h1081aM1685 : Magma (Fin 47)) big47h1081aM1685_models
    big47h1081a.E big47h1081a.Einv big47h1081a.rep big47h1081a.tr big47h1081a.z big47h1081a.st
    big47h1081a.hl big47h1081a.hr big47h1081aM1685_endo big47h1081a.htr big47h1081a.hz big47h1081a.hst
    nobig47h1081a_Law3279

theorem Equation3475_not_definableFrom_Equation1685 :
    ¬ Law3475.DefinableFrom Law1685 :=
  not_definableFrom_transportExact (big47h1081aM1685 : Magma (Fin 47)) big47h1081aM1685_models
    big47h1081a.E big47h1081a.Einv big47h1081a.rep big47h1081a.tr big47h1081a.z big47h1081a.st
    big47h1081a.hl big47h1081a.hr big47h1081aM1685_endo big47h1081a.htr big47h1081a.hz big47h1081a.hst
    nobig47h1081a_Law3475

theorem Equation3482_not_definableFrom_Equation1685 :
    ¬ Law3482.DefinableFrom Law1685 :=
  not_definableFrom_transportExact (big47h1081aM1685 : Magma (Fin 47)) big47h1081aM1685_models
    big47h1081a.E big47h1081a.Einv big47h1081a.rep big47h1081a.tr big47h1081a.z big47h1081a.st
    big47h1081a.hl big47h1081a.hr big47h1081aM1685_endo big47h1081a.htr big47h1081a.hz big47h1081a.hst
    nobig47h1081a_Law3482

theorem Equation14_not_definableFrom_Equation1286 :
    ¬ Law14.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law14

theorem Equation66_not_definableFrom_Equation1286 :
    ¬ Law66.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law66

theorem Equation115_not_definableFrom_Equation1286 :
    ¬ Law115.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law115

theorem Equation313_not_definableFrom_Equation1286 :
    ¬ Law313.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law313

theorem Equation477_not_definableFrom_Equation1286 :
    ¬ Law477.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law477

theorem Equation680_not_definableFrom_Equation1286 :
    ¬ Law680.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law680

theorem Equation873_not_definableFrom_Equation1286 :
    ¬ Law873.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law873

theorem Equation1083_not_definableFrom_Equation1286 :
    ¬ Law1083.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law1083

theorem Equation1276_not_definableFrom_Equation1286 :
    ¬ Law1276.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law1276

theorem Equation1519_not_definableFrom_Equation1286 :
    ¬ Law1519.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law1519

theorem Equation1719_not_definableFrom_Equation1286 :
    ¬ Law1719.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law1719

theorem Equation3272_not_definableFrom_Equation1286 :
    ¬ Law3272.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law3272

theorem Equation3472_not_definableFrom_Equation1286 :
    ¬ Law3472.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law3472

theorem Equation4273_not_definableFrom_Equation1286 :
    ¬ Law4273.DefinableFrom Law1286 :=
  not_definableFrom_transportExact (big59h1711aM1286 : Magma (Fin 59)) big59h1711aM1286_models
    big59h1711a.E big59h1711a.Einv big59h1711a.rep big59h1711a.tr big59h1711a.z big59h1711a.st
    big59h1711a.hl big59h1711a.hr big59h1711aM1286_endo big59h1711a.htr big59h1711a.hz big59h1711a.hst
    nobig59h1711a_Law4273

