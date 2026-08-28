import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 35 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 3,424 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3353 takes them (1057 nodes). -/
def ordS7R12_Law3353 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3353. -/
theorem noS7R12_Law3353 : ∀ v : Magma.tup7R12,
    ¬ @Equation3353 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3353) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3353) (by native_decide) v.1 v.2
    ((@Law3353.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (270 nodes). -/
def ordS7R12_Law3414 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3414. -/
theorem noS7R12_Law3414 : ∀ v : Magma.tup7R12,
    ¬ @Equation3414 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3458 takes them (991 nodes). -/
def ordS7R12_Law3458 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3458. -/
theorem noS7R12_Law3458 : ∀ v : Magma.tup7R12,
    ¬ @Equation3458 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3458) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3458) (by native_decide) v.1 v.2
    ((@Law3458.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3460 takes them (242 nodes). -/
def ordS7R12_Law3460 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3460. -/
theorem noS7R12_Law3460 : ∀ v : Magma.tup7R12,
    ¬ @Equation3460 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3460) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3460) (by native_decide) v.1 v.2
    ((@Law3460.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3467 takes them (436 nodes). -/
def ordS7R12_Law3467 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3467. -/
theorem noS7R12_Law3467 : ∀ v : Magma.tup7R12,
    ¬ @Equation3467 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3467) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3467) (by native_decide) v.1 v.2
    ((@Law3467.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3468 takes them (146 nodes). -/
def ordS7R12_Law3468 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3468. -/
theorem noS7R12_Law3468 : ∀ v : Magma.tup7R12,
    ¬ @Equation3468 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3468) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3468) (by native_decide) v.1 v.2
    ((@Law3468.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3470 takes them (38 nodes). -/
def ordS7R12_Law3470 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3470. -/
theorem noS7R12_Law3470 : ∀ v : Magma.tup7R12,
    ¬ @Equation3470 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3470) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3470) (by native_decide) v.1 v.2
    ((@Law3470.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3477 takes them (95 nodes). -/
def ordS7R12_Law3477 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3477. -/
theorem noS7R12_Law3477 : ∀ v : Magma.tup7R12,
    ¬ @Equation3477 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3477) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3477) (by native_decide) v.1 v.2
    ((@Law3477.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3478 takes them (149 nodes). -/
def ordS7R12_Law3478 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3478. -/
theorem noS7R12_Law3478 : ∀ v : Magma.tup7R12,
    ¬ @Equation3478 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3478) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3478) (by native_decide) v.1 v.2
    ((@Law3478.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch7R12_refutes_34 :
    FamilyRefutes Magma.srch7R12 [
      3353, 3414, 3458, 3460, 3467, 3468, 3470, 3477, 3478
    ] :=
  ⟨noS7R12_Law3353, noS7R12_Law3414, noS7R12_Law3458, noS7R12_Law3460, noS7R12_Law3467, noS7R12_Law3468, noS7R12_Law3470, noS7R12_Law3477, noS7R12_Law3478⟩
