import equational_theories.Definability.Srch_S8R43

/-!
# Structural certificate targets: `Magma.srch8R43` (part 4 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R43_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `18` equations here, 3,172 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R43_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4006 takes them (651 nodes). -/
def ordS8R43_Law4006 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4006. -/
theorem noS8R43_Law4006 : ∀ v : Magma.tup8R43,
    ¬ @Equation4006 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4006) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4006) (by native_decide) v.1 v.2
    ((@Law4006.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4040 takes them (392 nodes). -/
def ordS8R43_Law4040 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4040. -/
theorem noS8R43_Law4040 : ∀ v : Magma.tup8R43,
    ¬ @Equation4040 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4040) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4040) (by native_decide) v.1 v.2
    ((@Law4040.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4243 takes them (392 nodes). -/
def ordS8R43_Law4243 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4243. -/
theorem noS8R43_Law4243 : ∀ v : Magma.tup8R43,
    ¬ @Equation4243 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4243) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4243) (by native_decide) v.1 v.2
    ((@Law4243.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4437 takes them (108 nodes). -/
def ordS8R43_Law4437 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4437. -/
theorem noS8R43_Law4437 : ∀ v : Magma.tup8R43,
    ¬ @Equation4437 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4437) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4437) (by native_decide) v.1 v.2
    ((@Law4437.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4439 takes them (116 nodes). -/
def ordS8R43_Law4439 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4439. -/
theorem noS8R43_Law4439 : ∀ v : Magma.tup8R43,
    ¬ @Equation4439 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4439) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4439) (by native_decide) v.1 v.2
    ((@Law4439.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4441 takes them (62 nodes). -/
def ordS8R43_Law4441 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4441. -/
theorem noS8R43_Law4441 : ∀ v : Magma.tup8R43,
    ¬ @Equation4441 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4441) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4441) (by native_decide) v.1 v.2
    ((@Law4441.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4444 takes them (56 nodes). -/
def ordS8R43_Law4444 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4444. -/
theorem noS8R43_Law4444 : ∀ v : Magma.tup8R43,
    ¬ @Equation4444 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4444) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4444) (by native_decide) v.1 v.2
    ((@Law4444.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4448 takes them (160 nodes). -/
def ordS8R43_Law4448 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4448. -/
theorem noS8R43_Law4448 : ∀ v : Magma.tup8R43,
    ¬ @Equation4448 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4448) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4448) (by native_decide) v.1 v.2
    ((@Law4448.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4451 takes them (45 nodes). -/
def ordS8R43_Law4451 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4451. -/
theorem noS8R43_Law4451 : ∀ v : Magma.tup8R43,
    ¬ @Equation4451 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4451) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4451) (by native_decide) v.1 v.2
    ((@Law4451.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4453 takes them (86 nodes). -/
def ordS8R43_Law4453 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4453. -/
theorem noS8R43_Law4453 : ∀ v : Magma.tup8R43,
    ¬ @Equation4453 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4453) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4453) (by native_decide) v.1 v.2
    ((@Law4453.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4455 takes them (48 nodes). -/
def ordS8R43_Law4455 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4455. -/
theorem noS8R43_Law4455 : ∀ v : Magma.tup8R43,
    ¬ @Equation4455 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4455) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4455) (by native_decide) v.1 v.2
    ((@Law4455.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4456 takes them (370 nodes). -/
def ordS8R43_Law4456 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4456. -/
theorem noS8R43_Law4456 : ∀ v : Magma.tup8R43,
    ¬ @Equation4456 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4456) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4456) (by native_decide) v.1 v.2
    ((@Law4456.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4459 takes them (48 nodes). -/
def ordS8R43_Law4459 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4459. -/
theorem noS8R43_Law4459 : ∀ v : Magma.tup8R43,
    ¬ @Equation4459 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4459) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4459) (by native_decide) v.1 v.2
    ((@Law4459.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4464 takes them (141 nodes). -/
def ordS8R43_Law4464 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4464. -/
theorem noS8R43_Law4464 : ∀ v : Magma.tup8R43,
    ¬ @Equation4464 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4464) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4464) (by native_decide) v.1 v.2
    ((@Law4464.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4465 takes them (70 nodes). -/
def ordS8R43_Law4465 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4465. -/
theorem noS8R43_Law4465 : ∀ v : Magma.tup8R43,
    ¬ @Equation4465 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4465) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4465) (by native_decide) v.1 v.2
    ((@Law4465.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4468 takes them (45 nodes). -/
def ordS8R43_Law4468 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4468. -/
theorem noS8R43_Law4468 : ∀ v : Magma.tup8R43,
    ¬ @Equation4468 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4468) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 5)
    (ord := ordS8R43_Law4468) (by native_decide) v.1 v.2
    ((@Law4468.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4510 takes them (239 nodes). -/
def ordS8R43_Law4510 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4510. -/
theorem noS8R43_Law4510 : ∀ v : Magma.tup8R43,
    ¬ @Equation4510 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4510) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4510) (by native_decide) v.1 v.2
    ((@Law4510.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4514 takes them (143 nodes). -/
def ordS8R43_Law4514 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4514. -/
theorem noS8R43_Law4514 : ∀ v : Magma.tup8R43,
    ¬ @Equation4514 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4514) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4514) (by native_decide) v.1 v.2
    ((@Law4514.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- No member of the class satisfies any of these `18` equations. -/
theorem srch8R43_refutes_3 :
    FamilyRefutes Magma.srch8R43 [
      4006, 4040, 4243, 4437, 4439, 4441, 4444, 4448, 4451, 4453, 4455, 4456, 4459, 4464, 4465,
      4468, 4510, 4514
    ] :=
  ⟨noS8R43_Law4006, noS8R43_Law4040, noS8R43_Law4243, noS8R43_Law4437, noS8R43_Law4439, noS8R43_Law4441, noS8R43_Law4444, noS8R43_Law4448, noS8R43_Law4451, noS8R43_Law4453, noS8R43_Law4455, noS8R43_Law4456, noS8R43_Law4459, noS8R43_Law4464, noS8R43_Law4465, noS8R43_Law4468, noS8R43_Law4510, noS8R43_Law4514⟩
