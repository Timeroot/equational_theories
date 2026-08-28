import equational_theories.Definability.Srch_S7R15

/-!
# Structural certificate targets: `Magma.srch7R15`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R15_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `10` equations here, 2,176 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R15_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 127 takes them (163 nodes). -/
def ordS7R15_Law127 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 127. -/
theorem noS7R15_Law127 : ∀ v : Magma.tup7R15,
    ¬ @Equation127 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law127) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law127) (by native_decide) v.1 v.2
    ((@Law127.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 160 takes them (203 nodes). -/
def ordS7R15_Law160 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 160. -/
theorem noS7R15_Law160 : ∀ v : Magma.tup7R15,
    ¬ @Equation160 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law160) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law160) (by native_decide) v.1 v.2
    ((@Law160.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 179 takes them (155 nodes). -/
def ordS7R15_Law179 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 179. -/
theorem noS7R15_Law179 : ∀ v : Magma.tup7R15,
    ¬ @Equation179 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law179) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law179) (by native_decide) v.1 v.2
    ((@Law179.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 212 takes them (211 nodes). -/
def ordS7R15_Law212 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 212. -/
theorem noS7R15_Law212 : ∀ v : Magma.tup7R15,
    ¬ @Equation212 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law212) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law212) (by native_decide) v.1 v.2
    ((@Law212.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (321 nodes). -/
def ordS7R15_Law1278 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1278. -/
theorem noS7R15_Law1278 : ∀ v : Magma.tup7R15,
    ¬ @Equation1278 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (177 nodes). -/
def ordS7R15_Law1325 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1325. -/
theorem noS7R15_Law1325 : ∀ v : Magma.tup7R15,
    ¬ @Equation1325 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (224 nodes). -/
def ordS7R15_Law1455 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1455. -/
theorem noS7R15_Law1455 : ∀ v : Magma.tup7R15,
    ¬ @Equation1455 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (176 nodes). -/
def ordS7R15_Law2137 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2137. -/
theorem noS7R15_Law2137 : ∀ v : Magma.tup7R15,
    ¬ @Equation2137 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2254 takes them (321 nodes). -/
def ordS7R15_Law2254 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2254. -/
theorem noS7R15_Law2254 : ∀ v : Magma.tup7R15,
    ¬ @Equation2254 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2254) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law2254) (by native_decide) v.1 v.2
    ((@Law2254.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (225 nodes). -/
def ordS7R15_Law2267 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2267. -/
theorem noS7R15_Law2267 : ∀ v : Magma.tup7R15,
    ¬ @Equation2267 (Fin 7) (Magma.srch7R15 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S7R15.E) (tr := S7R15.tr) (z := S7R15.z)
    (st := S7R15.st) (X := S7R15.X) (envs := Magma.envsRed 7 S7R15.E 2)
    (ord := ordS7R15_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 7) (Magma.srch7R15 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch7R15_refutes_0 :
    FamilyRefutes Magma.srch7R15 [
      127, 160, 179, 212, 1278, 1325, 1455, 2137, 2254, 2267
    ] :=
  ⟨noS7R15_Law127, noS7R15_Law160, noS7R15_Law179, noS7R15_Law212, noS7R15_Law1278, noS7R15_Law1325, noS7R15_Law1455, noS7R15_Law2137, noS7R15_Law2254, noS7R15_Law2267⟩
