import equational_theories.Definability.Srch_S9R312

/-!
# Structural certificate targets: `Magma.srch9R312`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R312_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `14` equations here, 146 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R312_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 824 takes them (4 nodes). -/
def ordS9R312_Law824 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 824. -/
theorem noS9R312_Law824 : ∀ v : Magma.tup9R312,
    ¬ @Equation824 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law824) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law824) (by native_decide) v.1 v.2
    ((@Law824.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 828 takes them (6 nodes). -/
def ordS9R312_Law828 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 828. -/
theorem noS9R312_Law828 : ∀ v : Magma.tup9R312,
    ¬ @Equation828 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law828) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law828) (by native_decide) v.1 v.2
    ((@Law828.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 838 takes them (8 nodes). -/
def ordS9R312_Law838 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 838. -/
theorem noS9R312_Law838 : ∀ v : Magma.tup9R312,
    ¬ @Equation838 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law838) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law838) (by native_decide) v.1 v.2
    ((@Law838.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1233 takes them (6 nodes). -/
def ordS9R312_Law1233 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1233. -/
theorem noS9R312_Law1233 : ∀ v : Magma.tup9R312,
    ¬ @Equation1233 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1233) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law1233) (by native_decide) v.1 v.2
    ((@Law1233.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1236 takes them (6 nodes). -/
def ordS9R312_Law1236 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1236. -/
theorem noS9R312_Law1236 : ∀ v : Magma.tup9R312,
    ¬ @Equation1236 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1236) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law1236) (by native_decide) v.1 v.2
    ((@Law1236.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2347 takes them (6 nodes). -/
def ordS9R312_Law2347 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2347. -/
theorem noS9R312_Law2347 : ∀ v : Magma.tup9R312,
    ¬ @Equation2347 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2347) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law2347) (by native_decide) v.1 v.2
    ((@Law2347.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2398 takes them (6 nodes). -/
def ordS9R312_Law2398 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2398. -/
theorem noS9R312_Law2398 : ∀ v : Magma.tup9R312,
    ¬ @Equation2398 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2398) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law2398) (by native_decide) v.1 v.2
    ((@Law2398.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2665 takes them (8 nodes). -/
def ordS9R312_Law2665 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2665. -/
theorem noS9R312_Law2665 : ∀ v : Magma.tup9R312,
    ¬ @Equation2665 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2665) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law2665) (by native_decide) v.1 v.2
    ((@Law2665.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2679 takes them (6 nodes). -/
def ordS9R312_Law2679 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2679. -/
theorem noS9R312_Law2679 : ∀ v : Magma.tup9R312,
    ¬ @Equation2679 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2679) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law2679) (by native_decide) v.1 v.2
    ((@Law2679.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2716 takes them (4 nodes). -/
def ordS9R312_Law2716 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2716. -/
theorem noS9R312_Law2716 : ∀ v : Magma.tup9R312,
    ¬ @Equation2716 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2716) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 3)
    (ord := ordS9R312_Law2716) (by native_decide) v.1 v.2
    ((@Law2716.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3556 takes them (20 nodes). -/
def ordS9R312_Law3556 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3556. -/
theorem noS9R312_Law3556 : ∀ v : Magma.tup9R312,
    ¬ @Equation3556 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 2)
    (ord := ordS9R312_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3924 takes them (20 nodes). -/
def ordS9R312_Law3924 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3924. -/
theorem noS9R312_Law3924 : ∀ v : Magma.tup9R312,
    ¬ @Equation3924 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 2)
    (ord := ordS9R312_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4399 takes them (20 nodes). -/
def ordS9R312_Law4399 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4399. -/
theorem noS9R312_Law4399 : ∀ v : Magma.tup9R312,
    ¬ @Equation4399 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4399) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 2)
    (ord := ordS9R312_Law4399) (by native_decide) v.1 v.2
    ((@Law4399.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4435 takes them (26 nodes). -/
def ordS9R312_Law4435 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4435. -/
theorem noS9R312_Law4435 : ∀ v : Magma.tup9R312,
    ¬ @Equation4435 (Fin 9) (Magma.srch9R312 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4435) (E := S9R312.E) (tr := S9R312.tr) (z := S9R312.z)
    (st := S9R312.st) (X := S9R312.X) (envs := Magma.envsRed 9 S9R312.E 2)
    (ord := ordS9R312_Law4435) (by native_decide) v.1 v.2
    ((@Law4435.models_iff (Fin 9) (Magma.srch9R312 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch9R312_refutes_0 :
    FamilyRefutes Magma.srch9R312 [
      824, 828, 838, 1233, 1236, 2347, 2398, 2665, 2679, 2716, 3556, 3924, 4399, 4435
    ] :=
  ⟨noS9R312_Law824, noS9R312_Law828, noS9R312_Law838, noS9R312_Law1233, noS9R312_Law1236, noS9R312_Law2347, noS9R312_Law2398, noS9R312_Law2665, noS9R312_Law2679, noS9R312_Law2716, noS9R312_Law3556, noS9R312_Law3924, noS9R312_Law4399, noS9R312_Law4435⟩
