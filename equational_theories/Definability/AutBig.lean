import equational_theories.Definability.Aut_big16h240a
import equational_theories.Definability.Aut_big16h240a_L43
import equational_theories.Definability.Aut_big16h240a_L3342
import equational_theories.Definability.Aut_big16h240a_L3545
import equational_theories.Definability.Aut_big16h240a_L4405
import equational_theories.Definability.Aut_big29h406a
import equational_theories.Definability.Aut_big29h406a_L474

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

