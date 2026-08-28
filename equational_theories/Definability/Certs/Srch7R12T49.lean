import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 50 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 2,897 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4406 takes them (430 nodes). -/
def ordS7R12_Law4406 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4406. -/
theorem noS7R12_Law4406 : ∀ v : Magma.tup7R12,
    ¬ @Equation4406 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4406) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4406) (by native_decide) v.1 v.2
    ((@Law4406.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4412 takes them (89 nodes). -/
def ordS7R12_Law4412 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4412. -/
theorem noS7R12_Law4412 : ∀ v : Magma.tup7R12,
    ¬ @Equation4412 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4412) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4412) (by native_decide) v.1 v.2
    ((@Law4412.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4417 takes them (90 nodes). -/
def ordS7R12_Law4417 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4417. -/
theorem noS7R12_Law4417 : ∀ v : Magma.tup7R12,
    ¬ @Equation4417 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4417) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4417) (by native_decide) v.1 v.2
    ((@Law4417.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4421 takes them (92 nodes). -/
def ordS7R12_Law4421 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4421. -/
theorem noS7R12_Law4421 : ∀ v : Magma.tup7R12,
    ¬ @Equation4421 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4421) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4421) (by native_decide) v.1 v.2
    ((@Law4421.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4429 takes them (69 nodes). -/
def ordS7R12_Law4429 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4429. -/
theorem noS7R12_Law4429 : ∀ v : Magma.tup7R12,
    ¬ @Equation4429 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4429) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4429) (by native_decide) v.1 v.2
    ((@Law4429.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4432 takes them (785 nodes). -/
def ordS7R12_Law4432 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4432. -/
theorem noS7R12_Law4432 : ∀ v : Magma.tup7R12,
    ¬ @Equation4432 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4432) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4432) (by native_decide) v.1 v.2
    ((@Law4432.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4433 takes them (772 nodes). -/
def ordS7R12_Law4433 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4433. -/
theorem noS7R12_Law4433 : ∀ v : Magma.tup7R12,
    ¬ @Equation4433 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4433) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4433) (by native_decide) v.1 v.2
    ((@Law4433.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4434 takes them (570 nodes). -/
def ordS7R12_Law4434 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4434. -/
theorem noS7R12_Law4434 : ∀ v : Magma.tup7R12,
    ¬ @Equation4434 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4434) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4434) (by native_decide) v.1 v.2
    ((@Law4434.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch7R12_refutes_49 :
    FamilyRefutes Magma.srch7R12 [
      4406, 4412, 4417, 4421, 4429, 4432, 4433, 4434
    ] :=
  ⟨noS7R12_Law4406, noS7R12_Law4412, noS7R12_Law4417, noS7R12_Law4421, noS7R12_Law4429, noS7R12_Law4432, noS7R12_Law4433, noS7R12_Law4434⟩
