import equational_theories.Definability.Srch_S9R412

/-!
# Structural certificate targets: `Magma.srch9R412`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R412_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 1,162 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R412_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1249 takes them (102 nodes). -/
def ordS9R412_Law1249 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1249. -/
theorem noS9R412_Law1249 : ∀ v : Magma.tup9R412,
    ¬ @Equation1249 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1249) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 2)
    (ord := ordS9R412_Law1249) (by native_decide) v.1 v.2
    ((@Law1249.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (102 nodes). -/
def ordS9R412_Law1635 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1635. -/
theorem noS9R412_Law1635 : ∀ v : Magma.tup9R412,
    ¬ @Equation1635 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 2)
    (ord := ordS9R412_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1894 takes them (102 nodes). -/
def ordS9R412_Law1894 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1894. -/
theorem noS9R412_Law1894 : ∀ v : Magma.tup9R412,
    ¬ @Equation1894 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1894) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 2)
    (ord := ordS9R412_Law1894) (by native_decide) v.1 v.2
    ((@Law1894.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2303 takes them (102 nodes). -/
def ordS9R412_Law2303 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2303. -/
theorem noS9R412_Law2303 : ∀ v : Magma.tup9R412,
    ¬ @Equation2303 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2303) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 2)
    (ord := ordS9R412_Law2303) (by native_decide) v.1 v.2
    ((@Law2303.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3259 takes them (108 nodes). -/
def ordS9R412_Law3259 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3259. -/
theorem noS9R412_Law3259 : ∀ v : Magma.tup9R412,
    ¬ @Equation3259 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3259) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 2)
    (ord := ordS9R412_Law3259) (by native_decide) v.1 v.2
    ((@Law3259.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4083 takes them (108 nodes). -/
def ordS9R412_Law4083 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4083. -/
theorem noS9R412_Law4083 : ∀ v : Magma.tup9R412,
    ¬ @Equation4083 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4083) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 2)
    (ord := ordS9R412_Law4083) (by native_decide) v.1 v.2
    ((@Law4083.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4275 takes them (167 nodes). -/
def ordS9R412_Law4275 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4275. -/
theorem noS9R412_Law4275 : ∀ v : Magma.tup9R412,
    ¬ @Equation4275 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 2)
    (ord := ordS9R412_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4286 takes them (35 nodes). -/
def ordS9R412_Law4286 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4286. -/
theorem noS9R412_Law4286 : ∀ v : Magma.tup9R412,
    ¬ @Equation4286 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4286) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 3)
    (ord := ordS9R412_Law4286) (by native_decide) v.1 v.2
    ((@Law4286.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4307 takes them (67 nodes). -/
def ordS9R412_Law4307 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4307. -/
theorem noS9R412_Law4307 : ∀ v : Magma.tup9R412,
    ¬ @Equation4307 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 3)
    (ord := ordS9R412_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4585 takes them (167 nodes). -/
def ordS9R412_Law4585 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4585. -/
theorem noS9R412_Law4585 : ∀ v : Magma.tup9R412,
    ¬ @Equation4585 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4585) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 2)
    (ord := ordS9R412_Law4585) (by native_decide) v.1 v.2
    ((@Law4585.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4642 takes them (35 nodes). -/
def ordS9R412_Law4642 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4642. -/
theorem noS9R412_Law4642 : ∀ v : Magma.tup9R412,
    ¬ @Equation4642 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4642) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 3)
    (ord := ordS9R412_Law4642) (by native_decide) v.1 v.2
    ((@Law4642.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4656 takes them (67 nodes). -/
def ordS9R412_Law4656 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4656. -/
theorem noS9R412_Law4656 : ∀ v : Magma.tup9R412,
    ¬ @Equation4656 (Fin 9) (Magma.srch9R412 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4656) (E := S9R412.E) (tr := S9R412.tr) (z := S9R412.z)
    (st := S9R412.st) (X := S9R412.X) (envs := Magma.envsRed 9 S9R412.E 3)
    (ord := ordS9R412_Law4656) (by native_decide) v.1 v.2
    ((@Law4656.models_iff (Fin 9) (Magma.srch9R412 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch9R412_refutes_0 :
    FamilyRefutes Magma.srch9R412 [
      1249, 1635, 1894, 2303, 3259, 4083, 4275, 4286, 4307, 4585, 4642, 4656
    ] :=
  ⟨noS9R412_Law1249, noS9R412_Law1635, noS9R412_Law1894, noS9R412_Law2303, noS9R412_Law3259, noS9R412_Law4083, noS9R412_Law4275, noS9R412_Law4286, noS9R412_Law4307, noS9R412_Law4585, noS9R412_Law4642, noS9R412_Law4656⟩
