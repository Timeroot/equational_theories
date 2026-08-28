import equational_theories.Definability.Srch_S8R57

/-!
# Structural certificate targets: `Magma.srch8R57`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R57_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `32` equations here, 2,640 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R57_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 327 takes them (75 nodes). -/
def ordS8R57_Law327 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 327. -/
theorem noS8R57_Law327 : ∀ v : Magma.tup8R57,
    ¬ @Equation327 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law327) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law327) (by native_decide) v.1 v.2
    ((@Law327.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 395 takes them (75 nodes). -/
def ordS8R57_Law395 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 395. -/
theorem noS8R57_Law395 : ∀ v : Magma.tup8R57,
    ¬ @Equation395 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law395) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law395) (by native_decide) v.1 v.2
    ((@Law395.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1239 takes them (79 nodes). -/
def ordS8R57_Law1239 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1239. -/
theorem noS8R57_Law1239 : ∀ v : Magma.tup8R57,
    ¬ @Equation1239 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1239) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law1239) (by native_decide) v.1 v.2
    ((@Law1239.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1242 takes them (57 nodes). -/
def ordS8R57_Law1242 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1242. -/
theorem noS8R57_Law1242 : ∀ v : Magma.tup8R57,
    ¬ @Equation1242 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1242) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law1242) (by native_decide) v.1 v.2
    ((@Law1242.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1288 takes them (121 nodes). -/
def ordS8R57_Law1288 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1288. -/
theorem noS8R57_Law1288 : ∀ v : Magma.tup8R57,
    ¬ @Equation1288 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1288) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law1288) (by native_decide) v.1 v.2
    ((@Law1288.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (172 nodes). -/
def ordS8R57_Law1684 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1684. -/
theorem noS8R57_Law1684 : ∀ v : Magma.tup8R57,
    ¬ @Equation1684 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (172 nodes). -/
def ordS8R57_Law1848 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1848. -/
theorem noS8R57_Law1848 : ∀ v : Magma.tup8R57,
    ¬ @Equation1848 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2264 takes them (121 nodes). -/
def ordS8R57_Law2264 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2264. -/
theorem noS8R57_Law2264 : ∀ v : Magma.tup8R57,
    ¬ @Equation2264 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2264) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law2264) (by native_decide) v.1 v.2
    ((@Law2264.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2293 takes them (79 nodes). -/
def ordS8R57_Law2293 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2293. -/
theorem noS8R57_Law2293 : ∀ v : Magma.tup8R57,
    ¬ @Equation2293 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2293) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law2293) (by native_decide) v.1 v.2
    ((@Law2293.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2330 takes them (57 nodes). -/
def ordS8R57_Law2330 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2330. -/
theorem noS8R57_Law2330 : ∀ v : Magma.tup8R57,
    ¬ @Equation2330 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2330) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law2330) (by native_decide) v.1 v.2
    ((@Law2330.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3321 takes them (79 nodes). -/
def ordS8R57_Law3321 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3321. -/
theorem noS8R57_Law3321 : ∀ v : Magma.tup8R57,
    ¬ @Equation3321 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3321) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law3321) (by native_decide) v.1 v.2
    ((@Law3321.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3323 takes them (75 nodes). -/
def ordS8R57_Law3323 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3323. -/
theorem noS8R57_Law3323 : ∀ v : Magma.tup8R57,
    ¬ @Equation3323 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3323) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law3323) (by native_decide) v.1 v.2
    ((@Law3323.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3324 takes them (75 nodes). -/
def ordS8R57_Law3324 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3324. -/
theorem noS8R57_Law3324 : ∀ v : Magma.tup8R57,
    ¬ @Equation3324 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3324) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 4)
    (ord := ordS8R57_Law3324) (by native_decide) v.1 v.2
    ((@Law3324.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3326 takes them (51 nodes). -/
def ordS8R57_Law3326 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3326. -/
theorem noS8R57_Law3326 : ∀ v : Magma.tup8R57,
    ¬ @Equation3326 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3326) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law3326) (by native_decide) v.1 v.2
    ((@Law3326.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3462 takes them (110 nodes). -/
def ordS8R57_Law3462 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3462. -/
theorem noS8R57_Law3462 : ∀ v : Magma.tup8R57,
    ¬ @Equation3462 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3462) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law3462) (by native_decide) v.1 v.2
    ((@Law3462.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3529 takes them (111 nodes). -/
def ordS8R57_Law3529 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3529. -/
theorem noS8R57_Law3529 : ∀ v : Magma.tup8R57,
    ¬ @Equation3529 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3529) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law3529) (by native_decide) v.1 v.2
    ((@Law3529.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3537 takes them (44 nodes). -/
def ordS8R57_Law3537 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3537. -/
theorem noS8R57_Law3537 : ∀ v : Magma.tup8R57,
    ¬ @Equation3537 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3537) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law3537) (by native_decide) v.1 v.2
    ((@Law3537.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3541 takes them (44 nodes). -/
def ordS8R57_Law3541 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3541. -/
theorem noS8R57_Law3541 : ∀ v : Magma.tup8R57,
    ¬ @Equation3541 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3541) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 4)
    (ord := ordS8R57_Law3541) (by native_decide) v.1 v.2
    ((@Law3541.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3880 takes them (110 nodes). -/
def ordS8R57_Law3880 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3880. -/
theorem noS8R57_Law3880 : ∀ v : Magma.tup8R57,
    ¬ @Equation3880 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3880) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 2)
    (ord := ordS8R57_Law3880) (by native_decide) v.1 v.2
    ((@Law3880.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3931 takes them (111 nodes). -/
def ordS8R57_Law3931 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3931. -/
theorem noS8R57_Law3931 : ∀ v : Magma.tup8R57,
    ¬ @Equation3931 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3931) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law3931) (by native_decide) v.1 v.2
    ((@Law3931.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3943 takes them (44 nodes). -/
def ordS8R57_Law3943 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3943. -/
theorem noS8R57_Law3943 : ∀ v : Magma.tup8R57,
    ¬ @Equation3943 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3943) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law3943) (by native_decide) v.1 v.2
    ((@Law3943.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3947 takes them (44 nodes). -/
def ordS8R57_Law3947 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3947. -/
theorem noS8R57_Law3947 : ∀ v : Magma.tup8R57,
    ¬ @Equation3947 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3947) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 4)
    (ord := ordS8R57_Law3947) (by native_decide) v.1 v.2
    ((@Law3947.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4134 takes them (51 nodes). -/
def ordS8R57_Law4134 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4134. -/
theorem noS8R57_Law4134 : ∀ v : Magma.tup8R57,
    ¬ @Equation4134 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4134) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law4134) (by native_decide) v.1 v.2
    ((@Law4134.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4175 takes them (79 nodes). -/
def ordS8R57_Law4175 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4175. -/
theorem noS8R57_Law4175 : ∀ v : Magma.tup8R57,
    ¬ @Equation4175 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4175) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law4175) (by native_decide) v.1 v.2
    ((@Law4175.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4226 takes them (75 nodes). -/
def ordS8R57_Law4226 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4226. -/
theorem noS8R57_Law4226 : ∀ v : Magma.tup8R57,
    ¬ @Equation4226 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4226) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law4226) (by native_decide) v.1 v.2
    ((@Law4226.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4243 takes them (75 nodes). -/
def ordS8R57_Law4243 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4243. -/
theorem noS8R57_Law4243 : ∀ v : Magma.tup8R57,
    ¬ @Equation4243 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4243) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 4)
    (ord := ordS8R57_Law4243) (by native_decide) v.1 v.2
    ((@Law4243.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4287 takes them (89 nodes). -/
def ordS8R57_Law4287 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4287. -/
theorem noS8R57_Law4287 : ∀ v : Magma.tup8R57,
    ¬ @Equation4287 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4287) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law4287) (by native_decide) v.1 v.2
    ((@Law4287.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4340 takes them (69 nodes). -/
def ordS8R57_Law4340 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4340. -/
theorem noS8R57_Law4340 : ∀ v : Magma.tup8R57,
    ¬ @Equation4340 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4340) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law4340) (by native_decide) v.1 v.2
    ((@Law4340.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4360 takes them (69 nodes). -/
def ordS8R57_Law4360 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4360. -/
theorem noS8R57_Law4360 : ∀ v : Magma.tup8R57,
    ¬ @Equation4360 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4360) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 4)
    (ord := ordS8R57_Law4360) (by native_decide) v.1 v.2
    ((@Law4360.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4602 takes them (69 nodes). -/
def ordS8R57_Law4602 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4602. -/
theorem noS8R57_Law4602 : ∀ v : Magma.tup8R57,
    ¬ @Equation4602 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4602) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law4602) (by native_decide) v.1 v.2
    ((@Law4602.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4655 takes them (89 nodes). -/
def ordS8R57_Law4655 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4655. -/
theorem noS8R57_Law4655 : ∀ v : Magma.tup8R57,
    ¬ @Equation4655 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4655) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 3)
    (ord := ordS8R57_Law4655) (by native_decide) v.1 v.2
    ((@Law4655.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4675 takes them (69 nodes). -/
def ordS8R57_Law4675 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4675. -/
theorem noS8R57_Law4675 : ∀ v : Magma.tup8R57,
    ¬ @Equation4675 (Fin 8) (Magma.srch8R57 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4675) (E := S8R57.E) (tr := S8R57.tr) (z := S8R57.z)
    (st := S8R57.st) (X := S8R57.X) (envs := Magma.envsRed 8 S8R57.E 4)
    (ord := ordS8R57_Law4675) (by native_decide) v.1 v.2
    ((@Law4675.models_iff (Fin 8) (Magma.srch8R57 v)).mpr hv)

/-- No member of the class satisfies any of these `32` equations. -/
theorem srch8R57_refutes_0 :
    FamilyRefutes Magma.srch8R57 [
      327, 395, 1239, 1242, 1288, 1684, 1848, 2264, 2293, 2330, 3321, 3323, 3324, 3326, 3462,
      3529, 3537, 3541, 3880, 3931, 3943, 3947, 4134, 4175, 4226, 4243, 4287, 4340, 4360, 4602,
      4655, 4675
    ] :=
  ⟨noS8R57_Law327, noS8R57_Law395, noS8R57_Law1239, noS8R57_Law1242, noS8R57_Law1288, noS8R57_Law1684, noS8R57_Law1848, noS8R57_Law2264, noS8R57_Law2293, noS8R57_Law2330, noS8R57_Law3321, noS8R57_Law3323, noS8R57_Law3324, noS8R57_Law3326, noS8R57_Law3462, noS8R57_Law3529, noS8R57_Law3537, noS8R57_Law3541, noS8R57_Law3880, noS8R57_Law3931, noS8R57_Law3943, noS8R57_Law3947, noS8R57_Law4134, noS8R57_Law4175, noS8R57_Law4226, noS8R57_Law4243, noS8R57_Law4287, noS8R57_Law4340, noS8R57_Law4360, noS8R57_Law4602, noS8R57_Law4655, noS8R57_Law4675⟩
