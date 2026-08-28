import equational_theories.Definability.Srch_S8R2

/-!
# Structural certificate targets: `Magma.srch8R2` (part 69 of 260)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R2_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `10`
equations here, 3,186 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R2_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1207 takes them (109 nodes). -/
def ordS8R2_Law1207 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1207. -/
theorem noS8R2_Law1207 : ∀ v : Magma.tup8R2,
    ¬ @Equation1207 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1207) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law1207) (by native_decide) v.1 v.2
    ((@Law1207.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1212 takes them (109 nodes). -/
def ordS8R2_Law1212 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1212. -/
theorem noS8R2_Law1212 : ∀ v : Magma.tup8R2,
    ¬ @Equation1212 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1212) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law1212) (by native_decide) v.1 v.2
    ((@Law1212.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1217 takes them (109 nodes). -/
def ordS8R2_Law1217 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1217. -/
theorem noS8R2_Law1217 : ∀ v : Magma.tup8R2,
    ¬ @Equation1217 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1217) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 5)
    (ord := ordS8R2_Law1217) (by native_decide) v.1 v.2
    ((@Law1217.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1268 takes them (250 nodes). -/
def ordS8R2_Law1268 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1268. -/
theorem noS8R2_Law1268 : ∀ v : Magma.tup8R2,
    ¬ @Equation1268 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1268) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1268) (by native_decide) v.1 v.2
    ((@Law1268.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1269 takes them (46 nodes). -/
def ordS8R2_Law1269 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1269. -/
theorem noS8R2_Law1269 : ∀ v : Magma.tup8R2,
    ¬ @Equation1269 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1269) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law1269) (by native_decide) v.1 v.2
    ((@Law1269.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1272 takes them (197 nodes). -/
def ordS8R2_Law1272 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1272. -/
theorem noS8R2_Law1272 : ∀ v : Magma.tup8R2,
    ¬ @Equation1272 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1272) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law1272) (by native_decide) v.1 v.2
    ((@Law1272.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1273 takes them (206 nodes). -/
def ordS8R2_Law1273 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1273. -/
theorem noS8R2_Law1273 : ∀ v : Magma.tup8R2,
    ¬ @Equation1273 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1273) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law1273) (by native_decide) v.1 v.2
    ((@Law1273.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1274 takes them (46 nodes). -/
def ordS8R2_Law1274 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1274. -/
theorem noS8R2_Law1274 : ∀ v : Magma.tup8R2,
    ¬ @Equation1274 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1274) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 5)
    (ord := ordS8R2_Law1274) (by native_decide) v.1 v.2
    ((@Law1274.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1281 takes them (1417 nodes). -/
def ordS8R2_Law1281 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1281. -/
theorem noS8R2_Law1281 : ∀ v : Magma.tup8R2,
    ¬ @Equation1281 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1281) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1281) (by native_decide) v.1 v.2
    ((@Law1281.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1291 takes them (697 nodes). -/
def ordS8R2_Law1291 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 1291. -/
theorem noS8R2_Law1291 : ∀ v : Magma.tup8R2,
    ¬ @Equation1291 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1291) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law1291) (by native_decide) v.1 v.2
    ((@Law1291.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch8R2_refutes_68 :
    FamilyRefutes Magma.srch8R2 [
      1207, 1212, 1217, 1268, 1269, 1272, 1273, 1274, 1281, 1291
    ] :=
  ⟨noS8R2_Law1207, noS8R2_Law1212, noS8R2_Law1217, noS8R2_Law1268, noS8R2_Law1269, noS8R2_Law1272, noS8R2_Law1273, noS8R2_Law1274, noS8R2_Law1281, noS8R2_Law1291⟩
