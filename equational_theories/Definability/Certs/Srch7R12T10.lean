import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 11 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `11` equations here, 3,219 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1243 takes them (243 nodes). -/
def ordS7R12_Law1243 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1243. -/
theorem noS7R12_Law1243 : ∀ v : Magma.tup7R12,
    ¬ @Equation1243 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1243) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1243) (by native_decide) v.1 v.2
    ((@Law1243.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1245 takes them (119 nodes). -/
def ordS7R12_Law1245 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1245. -/
theorem noS7R12_Law1245 : ∀ v : Magma.tup7R12,
    ¬ @Equation1245 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1245) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1245) (by native_decide) v.1 v.2
    ((@Law1245.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1259 takes them (111 nodes). -/
def ordS7R12_Law1259 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1259. -/
theorem noS7R12_Law1259 : ∀ v : Magma.tup7R12,
    ¬ @Equation1259 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1259) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1259) (by native_decide) v.1 v.2
    ((@Law1259.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1260 takes them (115 nodes). -/
def ordS7R12_Law1260 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1260. -/
theorem noS7R12_Law1260 : ∀ v : Magma.tup7R12,
    ¬ @Equation1260 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1260) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1260) (by native_decide) v.1 v.2
    ((@Law1260.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1262 takes them (343 nodes). -/
def ordS7R12_Law1262 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1262. -/
theorem noS7R12_Law1262 : ∀ v : Magma.tup7R12,
    ¬ @Equation1262 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1262) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1262) (by native_decide) v.1 v.2
    ((@Law1262.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1265 takes them (168 nodes). -/
def ordS7R12_Law1265 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1265. -/
theorem noS7R12_Law1265 : ∀ v : Magma.tup7R12,
    ¬ @Equation1265 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1265) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law1265) (by native_decide) v.1 v.2
    ((@Law1265.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1266 takes them (259 nodes). -/
def ordS7R12_Law1266 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1266. -/
theorem noS7R12_Law1266 : ∀ v : Magma.tup7R12,
    ¬ @Equation1266 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1266) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1266) (by native_decide) v.1 v.2
    ((@Law1266.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1270 takes them (211 nodes). -/
def ordS7R12_Law1270 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1270. -/
theorem noS7R12_Law1270 : ∀ v : Magma.tup7R12,
    ¬ @Equation1270 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1270) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law1270) (by native_decide) v.1 v.2
    ((@Law1270.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1271 takes them (70 nodes). -/
def ordS7R12_Law1271 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1271. -/
theorem noS7R12_Law1271 : ∀ v : Magma.tup7R12,
    ¬ @Equation1271 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1271) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law1271) (by native_decide) v.1 v.2
    ((@Law1271.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (738 nodes). -/
def ordS7R12_Law1278 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1278. -/
theorem noS7R12_Law1278 : ∀ v : Magma.tup7R12,
    ¬ @Equation1278 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (842 nodes). -/
def ordS7R12_Law1325 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1325. -/
theorem noS7R12_Law1325 : ∀ v : Magma.tup7R12,
    ¬ @Equation1325 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch7R12_refutes_10 :
    FamilyRefutes Magma.srch7R12 [
      1243, 1245, 1259, 1260, 1262, 1265, 1266, 1270, 1271, 1278, 1325
    ] :=
  ⟨noS7R12_Law1243, noS7R12_Law1245, noS7R12_Law1259, noS7R12_Law1260, noS7R12_Law1262, noS7R12_Law1265, noS7R12_Law1266, noS7R12_Law1270, noS7R12_Law1271, noS7R12_Law1278, noS7R12_Law1325⟩
