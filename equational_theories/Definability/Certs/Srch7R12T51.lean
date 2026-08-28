import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 52 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,499 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4446 takes them (634 nodes). -/
def ordS7R12_Law4446 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4446. -/
theorem noS7R12_Law4446 : ∀ v : Magma.tup7R12,
    ¬ @Equation4446 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4446) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4446) (by native_decide) v.1 v.2
    ((@Law4446.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4447 takes them (562 nodes). -/
def ordS7R12_Law4447 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4447. -/
theorem noS7R12_Law4447 : ∀ v : Magma.tup7R12,
    ¬ @Equation4447 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4447) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4447) (by native_decide) v.1 v.2
    ((@Law4447.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4449 takes them (59 nodes). -/
def ordS7R12_Law4449 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4449. -/
theorem noS7R12_Law4449 : ∀ v : Magma.tup7R12,
    ¬ @Equation4449 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4449) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4449) (by native_decide) v.1 v.2
    ((@Law4449.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4450 takes them (82 nodes). -/
def ordS7R12_Law4450 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4450. -/
theorem noS7R12_Law4450 : ∀ v : Magma.tup7R12,
    ¬ @Equation4450 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4450) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4450) (by native_decide) v.1 v.2
    ((@Law4450.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4452 takes them (104 nodes). -/
def ordS7R12_Law4452 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4452. -/
theorem noS7R12_Law4452 : ∀ v : Magma.tup7R12,
    ¬ @Equation4452 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4452) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4452) (by native_decide) v.1 v.2
    ((@Law4452.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4454 takes them (73 nodes). -/
def ordS7R12_Law4454 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4454. -/
theorem noS7R12_Law4454 : ∀ v : Magma.tup7R12,
    ¬ @Equation4454 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4454) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4454) (by native_decide) v.1 v.2
    ((@Law4454.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4456 takes them (72 nodes). -/
def ordS7R12_Law4456 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4456. -/
theorem noS7R12_Law4456 : ∀ v : Magma.tup7R12,
    ¬ @Equation4456 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4456) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4456) (by native_decide) v.1 v.2
    ((@Law4456.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4457 takes them (86 nodes). -/
def ordS7R12_Law4457 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4457. -/
theorem noS7R12_Law4457 : ∀ v : Magma.tup7R12,
    ¬ @Equation4457 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4457) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4457) (by native_decide) v.1 v.2
    ((@Law4457.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4458 takes them (84 nodes). -/
def ordS7R12_Law4458 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4458. -/
theorem noS7R12_Law4458 : ∀ v : Magma.tup7R12,
    ¬ @Equation4458 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4458) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4458) (by native_decide) v.1 v.2
    ((@Law4458.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4460 takes them (574 nodes). -/
def ordS7R12_Law4460 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4460. -/
theorem noS7R12_Law4460 : ∀ v : Magma.tup7R12,
    ¬ @Equation4460 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4460) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4460) (by native_decide) v.1 v.2
    ((@Law4460.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4461 takes them (562 nodes). -/
def ordS7R12_Law4461 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4461. -/
theorem noS7R12_Law4461 : ∀ v : Magma.tup7R12,
    ¬ @Equation4461 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4461) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4461) (by native_decide) v.1 v.2
    ((@Law4461.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4462 takes them (607 nodes). -/
def ordS7R12_Law4462 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4462. -/
theorem noS7R12_Law4462 : ∀ v : Magma.tup7R12,
    ¬ @Equation4462 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4462) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4462) (by native_decide) v.1 v.2
    ((@Law4462.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch7R12_refutes_51 :
    FamilyRefutes Magma.srch7R12 [
      4446, 4447, 4449, 4450, 4452, 4454, 4456, 4457, 4458, 4460, 4461, 4462
    ] :=
  ⟨noS7R12_Law4446, noS7R12_Law4447, noS7R12_Law4449, noS7R12_Law4450, noS7R12_Law4452, noS7R12_Law4454, noS7R12_Law4456, noS7R12_Law4457, noS7R12_Law4458, noS7R12_Law4460, noS7R12_Law4461, noS7R12_Law4462⟩
