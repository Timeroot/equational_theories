import equational_theories.Definability.Srch_S9R1000

/-!
# Structural certificate targets: `Magma.srch9R1000`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R1000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `54` equations here, 678 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R1000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 101 takes them (12 nodes). -/
def ordS9R1000_Law101 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 101. -/
theorem noS9R1000_Law101 : ∀ v : Magma.tup9R1000,
    ¬ @Equation101 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law101) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law101) (by native_decide) v.1 v.2
    ((@Law101.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 104 takes them (12 nodes). -/
def ordS9R1000_Law104 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 104. -/
theorem noS9R1000_Law104 : ∀ v : Magma.tup9R1000,
    ¬ @Equation104 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law104) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law104) (by native_decide) v.1 v.2
    ((@Law104.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 205 takes them (12 nodes). -/
def ordS9R1000_Law205 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 205. -/
theorem noS9R1000_Law205 : ∀ v : Magma.tup9R1000,
    ¬ @Equation205 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law205) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law205) (by native_decide) v.1 v.2
    ((@Law205.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 208 takes them (12 nodes). -/
def ordS9R1000_Law208 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 208. -/
theorem noS9R1000_Law208 : ∀ v : Magma.tup9R1000,
    ¬ @Equation208 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law208) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law208) (by native_decide) v.1 v.2
    ((@Law208.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 413 takes them (12 nodes). -/
def ordS9R1000_Law413 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 413. -/
theorem noS9R1000_Law413 : ∀ v : Magma.tup9R1000,
    ¬ @Equation413 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law413) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law413) (by native_decide) v.1 v.2
    ((@Law413.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 419 takes them (17 nodes). -/
def ordS9R1000_Law419 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 419. -/
theorem noS9R1000_Law419 : ∀ v : Magma.tup9R1000,
    ¬ @Equation419 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law419) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law419) (by native_decide) v.1 v.2
    ((@Law419.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 429 takes them (12 nodes). -/
def ordS9R1000_Law429 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 429. -/
theorem noS9R1000_Law429 : ∀ v : Magma.tup9R1000,
    ¬ @Equation429 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law429) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law429) (by native_decide) v.1 v.2
    ((@Law429.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 622 takes them (12 nodes). -/
def ordS9R1000_Law622 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 622. -/
theorem noS9R1000_Law622 : ∀ v : Magma.tup9R1000,
    ¬ @Equation622 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law622) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law622) (by native_decide) v.1 v.2
    ((@Law622.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 819 takes them (12 nodes). -/
def ordS9R1000_Law819 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 819. -/
theorem noS9R1000_Law819 : ∀ v : Magma.tup9R1000,
    ¬ @Equation819 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law819) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law819) (by native_decide) v.1 v.2
    ((@Law819.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 825 takes them (12 nodes). -/
def ordS9R1000_Law825 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 825. -/
theorem noS9R1000_Law825 : ∀ v : Magma.tup9R1000,
    ¬ @Equation825 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law825) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law825) (by native_decide) v.1 v.2
    ((@Law825.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 832 takes them (12 nodes). -/
def ordS9R1000_Law832 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 832. -/
theorem noS9R1000_Law832 : ∀ v : Magma.tup9R1000,
    ¬ @Equation832 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law832) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law832) (by native_decide) v.1 v.2
    ((@Law832.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1022 takes them (12 nodes). -/
def ordS9R1000_Law1022 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1022. -/
theorem noS9R1000_Law1022 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1022 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1022) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1022) (by native_decide) v.1 v.2
    ((@Law1022.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1025 takes them (12 nodes). -/
def ordS9R1000_Law1025 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1025. -/
theorem noS9R1000_Law1025 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1025 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1025) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1025) (by native_decide) v.1 v.2
    ((@Law1025.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1028 takes them (12 nodes). -/
def ordS9R1000_Law1028 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1028. -/
theorem noS9R1000_Law1028 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1028 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1028) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1028) (by native_decide) v.1 v.2
    ((@Law1028.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1031 takes them (12 nodes). -/
def ordS9R1000_Law1031 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1031. -/
theorem noS9R1000_Law1031 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1031 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1031) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 3)
    (ord := ordS9R1000_Law1031) (by native_decide) v.1 v.2
    ((@Law1031.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1035 takes them (12 nodes). -/
def ordS9R1000_Law1035 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1035. -/
theorem noS9R1000_Law1035 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1035 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1035) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1035) (by native_decide) v.1 v.2
    ((@Law1035.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1045 takes them (17 nodes). -/
def ordS9R1000_Law1045 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1045. -/
theorem noS9R1000_Law1045 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1045 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1045) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1045) (by native_decide) v.1 v.2
    ((@Law1045.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1225 takes them (12 nodes). -/
def ordS9R1000_Law1225 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1225. -/
theorem noS9R1000_Law1225 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1225 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1225) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1225) (by native_decide) v.1 v.2
    ((@Law1225.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1228 takes them (12 nodes). -/
def ordS9R1000_Law1228 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1228. -/
theorem noS9R1000_Law1228 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1228 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1228) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1228) (by native_decide) v.1 v.2
    ((@Law1228.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1231 takes them (17 nodes). -/
def ordS9R1000_Law1231 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1231. -/
theorem noS9R1000_Law1231 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1231 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1231) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1231) (by native_decide) v.1 v.2
    ((@Law1231.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1238 takes them (12 nodes). -/
def ordS9R1000_Law1238 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1238. -/
theorem noS9R1000_Law1238 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1238 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1238) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1238) (by native_decide) v.1 v.2
    ((@Law1238.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1248 takes them (12 nodes). -/
def ordS9R1000_Law1248 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1248. -/
theorem noS9R1000_Law1248 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1248 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1248) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1248) (by native_decide) v.1 v.2
    ((@Law1248.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1258 takes them (12 nodes). -/
def ordS9R1000_Law1258 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1258. -/
theorem noS9R1000_Law1258 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1258 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1258) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 3)
    (ord := ordS9R1000_Law1258) (by native_decide) v.1 v.2
    ((@Law1258.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1428 takes them (12 nodes). -/
def ordS9R1000_Law1428 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1428. -/
theorem noS9R1000_Law1428 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1428 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1428) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1428) (by native_decide) v.1 v.2
    ((@Law1428.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1631 takes them (12 nodes). -/
def ordS9R1000_Law1631 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1631. -/
theorem noS9R1000_Law1631 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1631 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1631) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1631) (by native_decide) v.1 v.2
    ((@Law1631.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1634 takes them (12 nodes). -/
def ordS9R1000_Law1634 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1634. -/
theorem noS9R1000_Law1634 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1634 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1634) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1634) (by native_decide) v.1 v.2
    ((@Law1634.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1837 takes them (12 nodes). -/
def ordS9R1000_Law1837 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1837. -/
theorem noS9R1000_Law1837 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1837 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1837) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1837) (by native_decide) v.1 v.2
    ((@Law1837.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1847 takes them (12 nodes). -/
def ordS9R1000_Law1847 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1847. -/
theorem noS9R1000_Law1847 : ∀ v : Magma.tup9R1000,
    ¬ @Equation1847 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1847) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law1847) (by native_decide) v.1 v.2
    ((@Law1847.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2050 takes them (12 nodes). -/
def ordS9R1000_Law2050 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2050. -/
theorem noS9R1000_Law2050 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2050 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2050) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2050) (by native_decide) v.1 v.2
    ((@Law2050.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2240 takes them (12 nodes). -/
def ordS9R1000_Law2240 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2240. -/
theorem noS9R1000_Law2240 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2240 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2240) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2240) (by native_decide) v.1 v.2
    ((@Law2240.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2243 takes them (12 nodes). -/
def ordS9R1000_Law2243 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2243. -/
theorem noS9R1000_Law2243 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2243 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2243) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2243) (by native_decide) v.1 v.2
    ((@Law2243.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2246 takes them (12 nodes). -/
def ordS9R1000_Law2246 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2246. -/
theorem noS9R1000_Law2246 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2246 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2246) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2246) (by native_decide) v.1 v.2
    ((@Law2246.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2249 takes them (12 nodes). -/
def ordS9R1000_Law2249 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2249. -/
theorem noS9R1000_Law2249 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2249 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2249) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 3)
    (ord := ordS9R1000_Law2249) (by native_decide) v.1 v.2
    ((@Law2249.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2253 takes them (12 nodes). -/
def ordS9R1000_Law2253 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2253. -/
theorem noS9R1000_Law2253 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2253 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2253) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2253) (by native_decide) v.1 v.2
    ((@Law2253.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2263 takes them (17 nodes). -/
def ordS9R1000_Law2263 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2263. -/
theorem noS9R1000_Law2263 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2263 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2263) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2263) (by native_decide) v.1 v.2
    ((@Law2263.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2443 takes them (12 nodes). -/
def ordS9R1000_Law2443 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2443. -/
theorem noS9R1000_Law2443 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2443 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2443) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2443) (by native_decide) v.1 v.2
    ((@Law2443.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2446 takes them (12 nodes). -/
def ordS9R1000_Law2446 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2446. -/
theorem noS9R1000_Law2446 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2446 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2446) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2446) (by native_decide) v.1 v.2
    ((@Law2446.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2449 takes them (17 nodes). -/
def ordS9R1000_Law2449 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2449. -/
theorem noS9R1000_Law2449 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2449 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2449) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2449) (by native_decide) v.1 v.2
    ((@Law2449.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2456 takes them (12 nodes). -/
def ordS9R1000_Law2456 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2456. -/
theorem noS9R1000_Law2456 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2456 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2456) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2456) (by native_decide) v.1 v.2
    ((@Law2456.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2466 takes them (12 nodes). -/
def ordS9R1000_Law2466 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2466. -/
theorem noS9R1000_Law2466 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2466 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2466) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2466) (by native_decide) v.1 v.2
    ((@Law2466.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2476 takes them (12 nodes). -/
def ordS9R1000_Law2476 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2476. -/
theorem noS9R1000_Law2476 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2476 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2476) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 3)
    (ord := ordS9R1000_Law2476) (by native_decide) v.1 v.2
    ((@Law2476.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2646 takes them (12 nodes). -/
def ordS9R1000_Law2646 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2646. -/
theorem noS9R1000_Law2646 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2646 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2646) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2646) (by native_decide) v.1 v.2
    ((@Law2646.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2659 takes them (12 nodes). -/
def ordS9R1000_Law2659 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2659. -/
theorem noS9R1000_Law2659 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2659 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2659) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2659) (by native_decide) v.1 v.2
    ((@Law2659.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2669 takes them (12 nodes). -/
def ordS9R1000_Law2669 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2669. -/
theorem noS9R1000_Law2669 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2669 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2669) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2669) (by native_decide) v.1 v.2
    ((@Law2669.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2872 takes them (12 nodes). -/
def ordS9R1000_Law2872 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2872. -/
theorem noS9R1000_Law2872 : ∀ v : Magma.tup9R1000,
    ¬ @Equation2872 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2872) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law2872) (by native_decide) v.1 v.2
    ((@Law2872.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3065 takes them (12 nodes). -/
def ordS9R1000_Law3065 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3065. -/
theorem noS9R1000_Law3065 : ∀ v : Magma.tup9R1000,
    ¬ @Equation3065 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3065) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law3065) (by native_decide) v.1 v.2
    ((@Law3065.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3068 takes them (12 nodes). -/
def ordS9R1000_Law3068 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3068. -/
theorem noS9R1000_Law3068 : ∀ v : Magma.tup9R1000,
    ¬ @Equation3068 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3068) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law3068) (by native_decide) v.1 v.2
    ((@Law3068.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3075 takes them (17 nodes). -/
def ordS9R1000_Law3075 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3075. -/
theorem noS9R1000_Law3075 : ∀ v : Magma.tup9R1000,
    ¬ @Equation3075 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3075) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law3075) (by native_decide) v.1 v.2
    ((@Law3075.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3255 takes them (12 nodes). -/
def ordS9R1000_Law3255 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3255. -/
theorem noS9R1000_Law3255 : ∀ v : Magma.tup9R1000,
    ¬ @Equation3255 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3255) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law3255) (by native_decide) v.1 v.2
    ((@Law3255.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3458 takes them (12 nodes). -/
def ordS9R1000_Law3458 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3458. -/
theorem noS9R1000_Law3458 : ∀ v : Magma.tup9R1000,
    ¬ @Equation3458 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3458) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law3458) (by native_decide) v.1 v.2
    ((@Law3458.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3461 takes them (12 nodes). -/
def ordS9R1000_Law3461 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3461. -/
theorem noS9R1000_Law3461 : ∀ v : Magma.tup9R1000,
    ¬ @Equation3461 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3461) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law3461) (by native_decide) v.1 v.2
    ((@Law3461.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3864 takes them (12 nodes). -/
def ordS9R1000_Law3864 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3864. -/
theorem noS9R1000_Law3864 : ∀ v : Magma.tup9R1000,
    ¬ @Equation3864 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3864) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law3864) (by native_decide) v.1 v.2
    ((@Law3864.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3867 takes them (12 nodes). -/
def ordS9R1000_Law3867 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3867. -/
theorem noS9R1000_Law3867 : ∀ v : Magma.tup9R1000,
    ¬ @Equation3867 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3867) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law3867) (by native_decide) v.1 v.2
    ((@Law3867.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4070 takes them (12 nodes). -/
def ordS9R1000_Law4070 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4070. -/
theorem noS9R1000_Law4070 : ∀ v : Magma.tup9R1000,
    ¬ @Equation4070 (Fin 9) (Magma.srch9R1000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4070) (E := S9R1000.E) (tr := S9R1000.tr) (z := S9R1000.z)
    (st := S9R1000.st) (X := S9R1000.X) (envs := Magma.envsRed 9 S9R1000.E 2)
    (ord := ordS9R1000_Law4070) (by native_decide) v.1 v.2
    ((@Law4070.models_iff (Fin 9) (Magma.srch9R1000 v)).mpr hv)

/-- No member of the class satisfies any of these `54` equations. -/
theorem srch9R1000_refutes_0 :
    FamilyRefutes Magma.srch9R1000 [
      101, 104, 205, 208, 413, 419, 429, 622, 819, 825, 832, 1022, 1025, 1028, 1031, 1035, 1045,
      1225, 1228, 1231, 1238, 1248, 1258, 1428, 1631, 1634, 1837, 1847, 2050, 2240, 2243, 2246,
      2249, 2253, 2263, 2443, 2446, 2449, 2456, 2466, 2476, 2646, 2659, 2669, 2872, 3065, 3068,
      3075, 3255, 3458, 3461, 3864, 3867, 4070
    ] :=
  ⟨noS9R1000_Law101, noS9R1000_Law104, noS9R1000_Law205, noS9R1000_Law208, noS9R1000_Law413, noS9R1000_Law419, noS9R1000_Law429, noS9R1000_Law622, noS9R1000_Law819, noS9R1000_Law825, noS9R1000_Law832, noS9R1000_Law1022, noS9R1000_Law1025, noS9R1000_Law1028, noS9R1000_Law1031, noS9R1000_Law1035, noS9R1000_Law1045, noS9R1000_Law1225, noS9R1000_Law1228, noS9R1000_Law1231, noS9R1000_Law1238, noS9R1000_Law1248, noS9R1000_Law1258, noS9R1000_Law1428, noS9R1000_Law1631, noS9R1000_Law1634, noS9R1000_Law1837, noS9R1000_Law1847, noS9R1000_Law2050, noS9R1000_Law2240, noS9R1000_Law2243, noS9R1000_Law2246, noS9R1000_Law2249, noS9R1000_Law2253, noS9R1000_Law2263, noS9R1000_Law2443, noS9R1000_Law2446, noS9R1000_Law2449, noS9R1000_Law2456, noS9R1000_Law2466, noS9R1000_Law2476, noS9R1000_Law2646, noS9R1000_Law2659, noS9R1000_Law2669, noS9R1000_Law2872, noS9R1000_Law3065, noS9R1000_Law3068, noS9R1000_Law3075, noS9R1000_Law3255, noS9R1000_Law3458, noS9R1000_Law3461, noS9R1000_Law3864, noS9R1000_Law3867, noS9R1000_Law4070⟩
