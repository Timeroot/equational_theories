import equational_theories.Definability.Srch_S9R407

/-!
# Structural certificate targets: `Magma.srch9R407` (part 1 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R407_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `21` equations here, 2,979 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R407_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 106 takes them (82 nodes). -/
def ordS9R407_Law106 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 106. -/
theorem noS9R407_Law106 : ∀ v : Magma.tup9R407,
    ¬ @Equation106 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law106) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law106) (by native_decide) v.1 v.2
    ((@Law106.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 224 takes them (81 nodes). -/
def ordS9R407_Law224 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 224. -/
theorem noS9R407_Law224 : ∀ v : Magma.tup9R407,
    ¬ @Equation224 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law224) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law224) (by native_decide) v.1 v.2
    ((@Law224.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 325 takes them (344 nodes). -/
def ordS9R407_Law325 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 325. -/
theorem noS9R407_Law325 : ∀ v : Magma.tup9R407,
    ¬ @Equation325 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law325) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law325) (by native_decide) v.1 v.2
    ((@Law325.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 385 takes them (210 nodes). -/
def ordS9R407_Law385 : List (Fin 7) := [0, 3, 6, 2, 5, 1, 4]

/-- No member of the class satisfies equation 385. -/
theorem noS9R407_Law385 : ∀ v : Magma.tup9R407,
    ¬ @Equation385 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law385) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law385) (by native_decide) v.1 v.2
    ((@Law385.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 452 takes them (63 nodes). -/
def ordS9R407_Law452 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 452. -/
theorem noS9R407_Law452 : ∀ v : Magma.tup9R407,
    ¬ @Equation452 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law452) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law452) (by native_decide) v.1 v.2
    ((@Law452.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 655 takes them (65 nodes). -/
def ordS9R407_Law655 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 655. -/
theorem noS9R407_Law655 : ∀ v : Magma.tup9R407,
    ¬ @Equation655 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law655) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law655) (by native_decide) v.1 v.2
    ((@Law655.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 833 takes them (159 nodes). -/
def ordS9R407_Law833 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 833. -/
theorem noS9R407_Law833 : ∀ v : Magma.tup9R407,
    ¬ @Equation833 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law833) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law833) (by native_decide) v.1 v.2
    ((@Law833.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 834 takes them (89 nodes). -/
def ordS9R407_Law834 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 834. -/
theorem noS9R407_Law834 : ∀ v : Magma.tup9R407,
    ¬ @Equation834 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law834) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law834) (by native_decide) v.1 v.2
    ((@Law834.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 837 takes them (128 nodes). -/
def ordS9R407_Law837 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 837. -/
theorem noS9R407_Law837 : ∀ v : Magma.tup9R407,
    ¬ @Equation837 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law837) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law837) (by native_decide) v.1 v.2
    ((@Law837.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 839 takes them (90 nodes). -/
def ordS9R407_Law839 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 839. -/
theorem noS9R407_Law839 : ∀ v : Magma.tup9R407,
    ¬ @Equation839 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law839) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law839) (by native_decide) v.1 v.2
    ((@Law839.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 841 takes them (83 nodes). -/
def ordS9R407_Law841 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 841. -/
theorem noS9R407_Law841 : ∀ v : Magma.tup9R407,
    ¬ @Equation841 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law841) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 4)
    (ord := ordS9R407_Law841) (by native_decide) v.1 v.2
    ((@Law841.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 861 takes them (23 nodes). -/
def ordS9R407_Law861 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 861. -/
theorem noS9R407_Law861 : ∀ v : Magma.tup9R407,
    ¬ @Equation861 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law861) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law861) (by native_decide) v.1 v.2
    ((@Law861.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1061 takes them (108 nodes). -/
def ordS9R407_Law1061 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1061. -/
theorem noS9R407_Law1061 : ∀ v : Magma.tup9R407,
    ¬ @Equation1061 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1061) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law1061) (by native_decide) v.1 v.2
    ((@Law1061.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1246 takes them (168 nodes). -/
def ordS9R407_Law1246 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1246. -/
theorem noS9R407_Law1246 : ∀ v : Magma.tup9R407,
    ¬ @Equation1246 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1246) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law1246) (by native_decide) v.1 v.2
    ((@Law1246.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1247 takes them (85 nodes). -/
def ordS9R407_Law1247 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1247. -/
theorem noS9R407_Law1247 : ∀ v : Magma.tup9R407,
    ¬ @Equation1247 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1247) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 4)
    (ord := ordS9R407_Law1247) (by native_decide) v.1 v.2
    ((@Law1247.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1260 takes them (103 nodes). -/
def ordS9R407_Law1260 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1260. -/
theorem noS9R407_Law1260 : ∀ v : Magma.tup9R407,
    ¬ @Equation1260 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1260) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law1260) (by native_decide) v.1 v.2
    ((@Law1260.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1261 takes them (82 nodes). -/
def ordS9R407_Law1261 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1261. -/
theorem noS9R407_Law1261 : ∀ v : Magma.tup9R407,
    ¬ @Equation1261 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1261) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 4)
    (ord := ordS9R407_Law1261) (by native_decide) v.1 v.2
    ((@Law1261.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (245 nodes). -/
def ordS9R407_Law1442 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1442. -/
theorem noS9R407_Law1442 : ∀ v : Magma.tup9R407,
    ¬ @Equation1442 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1481 takes them (206 nodes). -/
def ordS9R407_Law1481 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1481. -/
theorem noS9R407_Law1481 : ∀ v : Magma.tup9R407,
    ¬ @Equation1481 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1481) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law1481) (by native_decide) v.1 v.2
    ((@Law1481.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (228 nodes). -/
def ordS9R407_Law1684 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1684. -/
theorem noS9R407_Law1684 : ∀ v : Magma.tup9R407,
    ¬ @Equation1684 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (337 nodes). -/
def ordS9R407_Law1848 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1848. -/
theorem noS9R407_Law1848 : ∀ v : Magma.tup9R407,
    ¬ @Equation1848 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- No member of the class satisfies any of these `21` equations. -/
theorem srch9R407_refutes_0 :
    FamilyRefutes Magma.srch9R407 [
      106, 224, 325, 385, 452, 655, 833, 834, 837, 839, 841, 861, 1061, 1246, 1247, 1260, 1261,
      1442, 1481, 1684, 1848
    ] :=
  ⟨noS9R407_Law106, noS9R407_Law224, noS9R407_Law325, noS9R407_Law385, noS9R407_Law452, noS9R407_Law655, noS9R407_Law833, noS9R407_Law834, noS9R407_Law837, noS9R407_Law839, noS9R407_Law841, noS9R407_Law861, noS9R407_Law1061, noS9R407_Law1246, noS9R407_Law1247, noS9R407_Law1260, noS9R407_Law1261, noS9R407_Law1442, noS9R407_Law1481, noS9R407_Law1684, noS9R407_Law1848⟩
