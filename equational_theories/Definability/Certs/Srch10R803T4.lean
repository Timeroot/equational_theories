import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 5 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 3,371 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1041 takes them (470 nodes). -/
def ordS10R803_Law1041 : List (Fin 8) := [2, 6, 0, 5, 7, 1, 4, 3]

/-- No member of the class satisfies equation 1041. -/
theorem noS10R803_Law1041 : ∀ v : Magma.tup10R803,
    ¬ @Equation1041 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1041) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1041) (by native_decide) v.1 v.2
    ((@Law1041.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1051 takes them (439 nodes). -/
def ordS10R803_Law1051 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1051. -/
theorem noS10R803_Law1051 : ∀ v : Magma.tup10R803,
    ¬ @Equation1051 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1051) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1051) (by native_decide) v.1 v.2
    ((@Law1051.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1055 takes them (467 nodes). -/
def ordS10R803_Law1055 : List (Fin 8) := [0, 1, 7, 2, 6, 3, 4, 5]

/-- No member of the class satisfies equation 1055. -/
theorem noS10R803_Law1055 : ∀ v : Magma.tup10R803,
    ¬ @Equation1055 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1055) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1055) (by native_decide) v.1 v.2
    ((@Law1055.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1056 takes them (186 nodes). -/
def ordS10R803_Law1056 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1056. -/
theorem noS10R803_Law1056 : ∀ v : Magma.tup10R803,
    ¬ @Equation1056 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1056) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1056) (by native_decide) v.1 v.2
    ((@Law1056.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1059 takes them (413 nodes). -/
def ordS10R803_Law1059 : List (Fin 8) := [6, 1, 3, 2, 7, 5, 0, 4]

/-- No member of the class satisfies equation 1059. -/
theorem noS10R803_Law1059 : ∀ v : Magma.tup10R803,
    ¬ @Equation1059 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1059) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1059) (by native_decide) v.1 v.2
    ((@Law1059.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1060 takes them (303 nodes). -/
def ordS10R803_Law1060 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1060. -/
theorem noS10R803_Law1060 : ∀ v : Magma.tup10R803,
    ¬ @Equation1060 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1060) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1060) (by native_decide) v.1 v.2
    ((@Law1060.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1067 takes them (439 nodes). -/
def ordS10R803_Law1067 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1067. -/
theorem noS10R803_Law1067 : ∀ v : Magma.tup10R803,
    ¬ @Equation1067 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1067) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law1067) (by native_decide) v.1 v.2
    ((@Law1067.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1068 takes them (186 nodes). -/
def ordS10R803_Law1068 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1068. -/
theorem noS10R803_Law1068 : ∀ v : Magma.tup10R803,
    ¬ @Equation1068 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1068) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law1068) (by native_decide) v.1 v.2
    ((@Law1068.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1230 takes them (468 nodes). -/
def ordS10R803_Law1230 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1230. -/
theorem noS10R803_Law1230 : ∀ v : Magma.tup10R803,
    ¬ @Equation1230 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1230) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1230) (by native_decide) v.1 v.2
    ((@Law1230.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch10R803_refutes_4 :
    FamilyRefutes Magma.srch10R803 [
      1041, 1051, 1055, 1056, 1059, 1060, 1067, 1068, 1230
    ] :=
  ⟨noS10R803_Law1041, noS10R803_Law1051, noS10R803_Law1055, noS10R803_Law1056, noS10R803_Law1059, noS10R803_Law1060, noS10R803_Law1067, noS10R803_Law1068, noS10R803_Law1230⟩
