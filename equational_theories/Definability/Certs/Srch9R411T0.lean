import equational_theories.Definability.Srch_S9R411

/-!
# Structural certificate targets: `Magma.srch9R411`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R411_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `18` equations here, 554 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R411_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 429 takes them (36 nodes). -/
def ordS9R411_Law429 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 429. -/
theorem noS9R411_Law429 : ∀ v : Magma.tup9R411,
    ¬ @Equation429 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law429) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law429) (by native_decide) v.1 v.2
    ((@Law429.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 632 takes them (31 nodes). -/
def ordS9R411_Law632 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 632. -/
theorem noS9R411_Law632 : ∀ v : Magma.tup9R411,
    ¬ @Equation632 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law632) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law632) (by native_decide) v.1 v.2
    ((@Law632.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 639 takes them (32 nodes). -/
def ordS9R411_Law639 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 639. -/
theorem noS9R411_Law639 : ∀ v : Magma.tup9R411,
    ¬ @Equation639 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law639) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law639) (by native_decide) v.1 v.2
    ((@Law639.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1023 takes them (34 nodes). -/
def ordS9R411_Law1023 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1023. -/
theorem noS9R411_Law1023 : ∀ v : Magma.tup9R411,
    ¬ @Equation1023 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1023) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law1023) (by native_decide) v.1 v.2
    ((@Law1023.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1026 takes them (22 nodes). -/
def ordS9R411_Law1026 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1026. -/
theorem noS9R411_Law1026 : ∀ v : Magma.tup9R411,
    ¬ @Equation1026 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1026) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law1026) (by native_decide) v.1 v.2
    ((@Law1026.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1229 takes them (28 nodes). -/
def ordS9R411_Law1229 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1229. -/
theorem noS9R411_Law1229 : ∀ v : Magma.tup9R411,
    ¬ @Equation1229 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1229) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law1229) (by native_decide) v.1 v.2
    ((@Law1229.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2300 takes them (28 nodes). -/
def ordS9R411_Law2300 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2300. -/
theorem noS9R411_Law2300 : ∀ v : Magma.tup9R411,
    ¬ @Equation2300 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2300) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law2300) (by native_decide) v.1 v.2
    ((@Law2300.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2503 takes them (21 nodes). -/
def ordS9R411_Law2503 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2503. -/
theorem noS9R411_Law2503 : ∀ v : Magma.tup9R411,
    ¬ @Equation2503 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2503) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law2503) (by native_decide) v.1 v.2
    ((@Law2503.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2530 takes them (33 nodes). -/
def ordS9R411_Law2530 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2530. -/
theorem noS9R411_Law2530 : ∀ v : Magma.tup9R411,
    ¬ @Equation2530 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2530) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law2530) (by native_decide) v.1 v.2
    ((@Law2530.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2855 takes them (35 nodes). -/
def ordS9R411_Law2855 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2855. -/
theorem noS9R411_Law2855 : ∀ v : Magma.tup9R411,
    ¬ @Equation2855 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2855) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law2855) (by native_decide) v.1 v.2
    ((@Law2855.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2865 takes them (32 nodes). -/
def ordS9R411_Law2865 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2865. -/
theorem noS9R411_Law2865 : ∀ v : Magma.tup9R411,
    ¬ @Equation2865 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2865) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law2865) (by native_decide) v.1 v.2
    ((@Law2865.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3068 takes them (41 nodes). -/
def ordS9R411_Law3068 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3068. -/
theorem noS9R411_Law3068 : ∀ v : Magma.tup9R411,
    ¬ @Equation3068 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3068) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law3068) (by native_decide) v.1 v.2
    ((@Law3068.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3271 takes them (27 nodes). -/
def ordS9R411_Law3271 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3271. -/
theorem noS9R411_Law3271 : ∀ v : Magma.tup9R411,
    ¬ @Equation3271 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3271) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law3271) (by native_decide) v.1 v.2
    ((@Law3271.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3474 takes them (24 nodes). -/
def ordS9R411_Law3474 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3474. -/
theorem noS9R411_Law3474 : ∀ v : Magma.tup9R411,
    ¬ @Equation3474 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3474) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law3474) (by native_decide) v.1 v.2
    ((@Law3474.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3481 takes them (38 nodes). -/
def ordS9R411_Law3481 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3481. -/
theorem noS9R411_Law3481 : ∀ v : Magma.tup9R411,
    ¬ @Equation3481 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3481) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law3481) (by native_decide) v.1 v.2
    ((@Law3481.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3865 takes them (38 nodes). -/
def ordS9R411_Law3865 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3865. -/
theorem noS9R411_Law3865 : ∀ v : Magma.tup9R411,
    ¬ @Equation3865 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3865) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law3865) (by native_decide) v.1 v.2
    ((@Law3865.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3868 takes them (24 nodes). -/
def ordS9R411_Law3868 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3868. -/
theorem noS9R411_Law3868 : ∀ v : Magma.tup9R411,
    ¬ @Equation3868 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3868) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law3868) (by native_decide) v.1 v.2
    ((@Law3868.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4071 takes them (30 nodes). -/
def ordS9R411_Law4071 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4071. -/
theorem noS9R411_Law4071 : ∀ v : Magma.tup9R411,
    ¬ @Equation4071 (Fin 9) (Magma.srch9R411 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4071) (E := S9R411.E) (tr := S9R411.tr) (z := S9R411.z)
    (st := S9R411.st) (X := S9R411.X) (envs := Magma.envsRed 9 S9R411.E 2)
    (ord := ordS9R411_Law4071) (by native_decide) v.1 v.2
    ((@Law4071.models_iff (Fin 9) (Magma.srch9R411 v)).mpr hv)

/-- No member of the class satisfies any of these `18` equations. -/
theorem srch9R411_refutes_0 :
    FamilyRefutes Magma.srch9R411 [
      429, 632, 639, 1023, 1026, 1229, 2300, 2503, 2530, 2855, 2865, 3068, 3271, 3474, 3481,
      3865, 3868, 4071
    ] :=
  ⟨noS9R411_Law429, noS9R411_Law632, noS9R411_Law639, noS9R411_Law1023, noS9R411_Law1026, noS9R411_Law1229, noS9R411_Law2300, noS9R411_Law2503, noS9R411_Law2530, noS9R411_Law2855, noS9R411_Law2865, noS9R411_Law3068, noS9R411_Law3271, noS9R411_Law3474, noS9R411_Law3481, noS9R411_Law3865, noS9R411_Law3868, noS9R411_Law4071⟩
