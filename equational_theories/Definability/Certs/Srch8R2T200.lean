import equational_theories.Definability.Srch_S8R2

/-!
# Structural certificate targets: `Magma.srch8R2` (part 201 of 260)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R2_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `14`
equations here, 3,359 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R2_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3095 takes them (783 nodes). -/
def ordS8R2_Law3095 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3095. -/
theorem noS8R2_Law3095 : ∀ v : Magma.tup8R2,
    ¬ @Equation3095 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3095) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law3095) (by native_decide) v.1 v.2
    ((@Law3095.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3096 takes them (131 nodes). -/
def ordS8R2_Law3096 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3096. -/
theorem noS8R2_Law3096 : ∀ v : Magma.tup8R2,
    ¬ @Equation3096 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3096) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law3096) (by native_decide) v.1 v.2
    ((@Law3096.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3098 takes them (463 nodes). -/
def ordS8R2_Law3098 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3098. -/
theorem noS8R2_Law3098 : ∀ v : Magma.tup8R2,
    ¬ @Equation3098 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3098) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law3098) (by native_decide) v.1 v.2
    ((@Law3098.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3099 takes them (495 nodes). -/
def ordS8R2_Law3099 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3099. -/
theorem noS8R2_Law3099 : ∀ v : Magma.tup8R2,
    ¬ @Equation3099 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3099) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law3099) (by native_decide) v.1 v.2
    ((@Law3099.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3100 takes them (703 nodes). -/
def ordS8R2_Law3100 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3100. -/
theorem noS8R2_Law3100 : ∀ v : Magma.tup8R2,
    ¬ @Equation3100 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3100) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law3100) (by native_decide) v.1 v.2
    ((@Law3100.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3101 takes them (131 nodes). -/
def ordS8R2_Law3101 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3101. -/
theorem noS8R2_Law3101 : ∀ v : Magma.tup8R2,
    ¬ @Equation3101 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3101) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 5)
    (ord := ordS8R2_Law3101) (by native_decide) v.1 v.2
    ((@Law3101.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3118 takes them (84 nodes). -/
def ordS8R2_Law3118 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3118. -/
theorem noS8R2_Law3118 : ∀ v : Magma.tup8R2,
    ¬ @Equation3118 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3118) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law3118) (by native_decide) v.1 v.2
    ((@Law3118.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3126 takes them (108 nodes). -/
def ordS8R2_Law3126 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3126. -/
theorem noS8R2_Law3126 : ∀ v : Magma.tup8R2,
    ¬ @Equation3126 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3126) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law3126) (by native_decide) v.1 v.2
    ((@Law3126.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3130 takes them (213 nodes). -/
def ordS8R2_Law3130 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3130. -/
theorem noS8R2_Law3130 : ∀ v : Magma.tup8R2,
    ¬ @Equation3130 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3130) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law3130) (by native_decide) v.1 v.2
    ((@Law3130.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3134 takes them (76 nodes). -/
def ordS8R2_Law3134 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3134. -/
theorem noS8R2_Law3134 : ∀ v : Magma.tup8R2,
    ¬ @Equation3134 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3134) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law3134) (by native_decide) v.1 v.2
    ((@Law3134.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3155 takes them (18 nodes). -/
def ordS8R2_Law3155 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3155. -/
theorem noS8R2_Law3155 : ∀ v : Magma.tup8R2,
    ¬ @Equation3155 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3155) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law3155) (by native_decide) v.1 v.2
    ((@Law3155.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3163 takes them (33 nodes). -/
def ordS8R2_Law3163 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3163. -/
theorem noS8R2_Law3163 : ∀ v : Magma.tup8R2,
    ¬ @Equation3163 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3163) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law3163) (by native_decide) v.1 v.2
    ((@Law3163.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3171 takes them (17 nodes). -/
def ordS8R2_Law3171 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3171. -/
theorem noS8R2_Law3171 : ∀ v : Magma.tup8R2,
    ¬ @Equation3171 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3171) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law3171) (by native_decide) v.1 v.2
    ((@Law3171.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3184 takes them (104 nodes). -/
def ordS8R2_Law3184 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 3184. -/
theorem noS8R2_Law3184 : ∀ v : Magma.tup8R2,
    ¬ @Equation3184 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3184) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law3184) (by native_decide) v.1 v.2
    ((@Law3184.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch8R2_refutes_200 :
    FamilyRefutes Magma.srch8R2 [
      3095, 3096, 3098, 3099, 3100, 3101, 3118, 3126, 3130, 3134, 3155, 3163, 3171, 3184
    ] :=
  ⟨noS8R2_Law3095, noS8R2_Law3096, noS8R2_Law3098, noS8R2_Law3099, noS8R2_Law3100, noS8R2_Law3101, noS8R2_Law3118, noS8R2_Law3126, noS8R2_Law3130, noS8R2_Law3134, noS8R2_Law3155, noS8R2_Law3163, noS8R2_Law3171, noS8R2_Law3184⟩
