import equational_theories.Definability.Srch_S8R43

/-!
# Structural certificate targets: `Magma.srch8R43` (part 1 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R43_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 3,385 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R43_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 106 takes them (149 nodes). -/
def ordS8R43_Law106 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 106. -/
theorem noS8R43_Law106 : ∀ v : Magma.tup8R43,
    ¬ @Equation106 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law106) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law106) (by native_decide) v.1 v.2
    ((@Law106.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 224 takes them (219 nodes). -/
def ordS8R43_Law224 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 224. -/
theorem noS8R43_Law224 : ∀ v : Magma.tup8R43,
    ¬ @Equation224 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law224) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law224) (by native_decide) v.1 v.2
    ((@Law224.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 327 takes them (326 nodes). -/
def ordS8R43_Law327 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 327. -/
theorem noS8R43_Law327 : ∀ v : Magma.tup8R43,
    ¬ @Equation327 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law327) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law327) (by native_decide) v.1 v.2
    ((@Law327.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 395 takes them (392 nodes). -/
def ordS8R43_Law395 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 395. -/
theorem noS8R43_Law395 : ∀ v : Magma.tup8R43,
    ¬ @Equation395 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law395) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law395) (by native_decide) v.1 v.2
    ((@Law395.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 837 takes them (218 nodes). -/
def ordS8R43_Law837 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 837. -/
theorem noS8R43_Law837 : ∀ v : Magma.tup8R43,
    ¬ @Equation837 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law837) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law837) (by native_decide) v.1 v.2
    ((@Law837.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 841 takes them (153 nodes). -/
def ordS8R43_Law841 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 841. -/
theorem noS8R43_Law841 : ∀ v : Magma.tup8R43,
    ¬ @Equation841 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law841) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law841) (by native_decide) v.1 v.2
    ((@Law841.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1246 takes them (255 nodes). -/
def ordS8R43_Law1246 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1246. -/
theorem noS8R43_Law1246 : ∀ v : Magma.tup8R43,
    ¬ @Equation1246 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1246) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law1246) (by native_decide) v.1 v.2
    ((@Law1246.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1247 takes them (146 nodes). -/
def ordS8R43_Law1247 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1247. -/
theorem noS8R43_Law1247 : ∀ v : Magma.tup8R43,
    ¬ @Equation1247 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1247) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law1247) (by native_decide) v.1 v.2
    ((@Law1247.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1261 takes them (149 nodes). -/
def ordS8R43_Law1261 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1261. -/
theorem noS8R43_Law1261 : ∀ v : Magma.tup8R43,
    ¬ @Equation1261 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1261) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law1261) (by native_decide) v.1 v.2
    ((@Law1261.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1655 takes them (450 nodes). -/
def ordS8R43_Law1655 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1655. -/
theorem noS8R43_Law1655 : ∀ v : Magma.tup8R43,
    ¬ @Equation1655 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1655) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 2)
    (ord := ordS8R43_Law1655) (by native_decide) v.1 v.2
    ((@Law1655.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1897 takes them (450 nodes). -/
def ordS8R43_Law1897 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1897. -/
theorem noS8R43_Law1897 : ∀ v : Magma.tup8R43,
    ¬ @Equation1897 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1897) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 2)
    (ord := ordS8R43_Law1897) (by native_decide) v.1 v.2
    ((@Law1897.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2322 takes them (225 nodes). -/
def ordS8R43_Law2322 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2322. -/
theorem noS8R43_Law2322 : ∀ v : Magma.tup8R43,
    ¬ @Equation2322 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2322) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law2322) (by native_decide) v.1 v.2
    ((@Law2322.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2333 takes them (253 nodes). -/
def ordS8R43_Law2333 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2333. -/
theorem noS8R43_Law2333 : ∀ v : Magma.tup8R43,
    ¬ @Equation2333 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2333) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law2333) (by native_decide) v.1 v.2
    ((@Law2333.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch8R43_refutes_0 :
    FamilyRefutes Magma.srch8R43 [
      106, 224, 327, 395, 837, 841, 1246, 1247, 1261, 1655, 1897, 2322, 2333
    ] :=
  ⟨noS8R43_Law106, noS8R43_Law224, noS8R43_Law327, noS8R43_Law395, noS8R43_Law837, noS8R43_Law841, noS8R43_Law1246, noS8R43_Law1247, noS8R43_Law1261, noS8R43_Law1655, noS8R43_Law1897, noS8R43_Law2322, noS8R43_Law2333⟩
