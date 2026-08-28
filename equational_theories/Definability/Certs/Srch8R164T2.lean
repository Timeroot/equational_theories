import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 3 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `74` equations here, 1,000 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1246 takes them (11 nodes). -/
def ordS8R164_Law1246 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1246. -/
theorem noS8R164_Law1246 : ∀ v : Magma.tup8R164,
    ¬ @Equation1246 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1246) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1246) (by native_decide) v.1 v.2
    ((@Law1246.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1247 takes them (10 nodes). -/
def ordS8R164_Law1247 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1247. -/
theorem noS8R164_Law1247 : ∀ v : Magma.tup8R164,
    ¬ @Equation1247 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1247) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law1247) (by native_decide) v.1 v.2
    ((@Law1247.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1258 takes them (18 nodes). -/
def ordS8R164_Law1258 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1258. -/
theorem noS8R164_Law1258 : ∀ v : Magma.tup8R164,
    ¬ @Equation1258 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1258) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1258) (by native_decide) v.1 v.2
    ((@Law1258.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1259 takes them (11 nodes). -/
def ordS8R164_Law1259 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1259. -/
theorem noS8R164_Law1259 : ∀ v : Magma.tup8R164,
    ¬ @Equation1259 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1259) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1259) (by native_decide) v.1 v.2
    ((@Law1259.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1260 takes them (11 nodes). -/
def ordS8R164_Law1260 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1260. -/
theorem noS8R164_Law1260 : ∀ v : Magma.tup8R164,
    ¬ @Equation1260 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1260) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1260) (by native_decide) v.1 v.2
    ((@Law1260.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1261 takes them (10 nodes). -/
def ordS8R164_Law1261 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1261. -/
theorem noS8R164_Law1261 : ∀ v : Magma.tup8R164,
    ¬ @Equation1261 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1261) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law1261) (by native_decide) v.1 v.2
    ((@Law1261.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1262 takes them (16 nodes). -/
def ordS8R164_Law1262 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1262. -/
theorem noS8R164_Law1262 : ∀ v : Magma.tup8R164,
    ¬ @Equation1262 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1262) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1262) (by native_decide) v.1 v.2
    ((@Law1262.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1263 takes them (11 nodes). -/
def ordS8R164_Law1263 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1263. -/
theorem noS8R164_Law1263 : ∀ v : Magma.tup8R164,
    ¬ @Equation1263 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1263) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1263) (by native_decide) v.1 v.2
    ((@Law1263.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1265 takes them (9 nodes). -/
def ordS8R164_Law1265 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1265. -/
theorem noS8R164_Law1265 : ∀ v : Magma.tup8R164,
    ¬ @Equation1265 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1265) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law1265) (by native_decide) v.1 v.2
    ((@Law1265.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1266 takes them (16 nodes). -/
def ordS8R164_Law1266 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1266. -/
theorem noS8R164_Law1266 : ∀ v : Magma.tup8R164,
    ¬ @Equation1266 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1266) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1266) (by native_decide) v.1 v.2
    ((@Law1266.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1270 takes them (16 nodes). -/
def ordS8R164_Law1270 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1270. -/
theorem noS8R164_Law1270 : ∀ v : Magma.tup8R164,
    ¬ @Equation1270 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1270) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law1270) (by native_decide) v.1 v.2
    ((@Law1270.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1271 takes them (10 nodes). -/
def ordS8R164_Law1271 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1271. -/
theorem noS8R164_Law1271 : ∀ v : Magma.tup8R164,
    ¬ @Equation1271 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1271) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law1271) (by native_decide) v.1 v.2
    ((@Law1271.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1427 takes them (8 nodes). -/
def ordS8R164_Law1427 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1427. -/
theorem noS8R164_Law1427 : ∀ v : Magma.tup8R164,
    ¬ @Equation1427 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1427) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1427) (by native_decide) v.1 v.2
    ((@Law1427.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1428 takes them (14 nodes). -/
def ordS8R164_Law1428 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1428. -/
theorem noS8R164_Law1428 : ∀ v : Magma.tup8R164,
    ¬ @Equation1428 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1428) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1428) (by native_decide) v.1 v.2
    ((@Law1428.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1430 takes them (8 nodes). -/
def ordS8R164_Law1430 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1430. -/
theorem noS8R164_Law1430 : ∀ v : Magma.tup8R164,
    ¬ @Equation1430 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1430) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1430) (by native_decide) v.1 v.2
    ((@Law1430.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1631 takes them (18 nodes). -/
def ordS8R164_Law1631 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1631. -/
theorem noS8R164_Law1631 : ∀ v : Magma.tup8R164,
    ¬ @Equation1631 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1631) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1631) (by native_decide) v.1 v.2
    ((@Law1631.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1634 takes them (15 nodes). -/
def ordS8R164_Law1634 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1634. -/
theorem noS8R164_Law1634 : ∀ v : Magma.tup8R164,
    ¬ @Equation1634 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1634) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1634) (by native_decide) v.1 v.2
    ((@Law1634.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1640 takes them (14 nodes). -/
def ordS8R164_Law1640 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1640. -/
theorem noS8R164_Law1640 : ∀ v : Magma.tup8R164,
    ¬ @Equation1640 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1640) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1640) (by native_decide) v.1 v.2
    ((@Law1640.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1644 takes them (17 nodes). -/
def ordS8R164_Law1644 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1644. -/
theorem noS8R164_Law1644 : ∀ v : Magma.tup8R164,
    ¬ @Equation1644 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1644) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1644) (by native_decide) v.1 v.2
    ((@Law1644.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1650 takes them (16 nodes). -/
def ordS8R164_Law1650 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1650. -/
theorem noS8R164_Law1650 : ∀ v : Magma.tup8R164,
    ¬ @Equation1650 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1650) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1650) (by native_decide) v.1 v.2
    ((@Law1650.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1657 takes them (16 nodes). -/
def ordS8R164_Law1657 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1657. -/
theorem noS8R164_Law1657 : ∀ v : Magma.tup8R164,
    ¬ @Equation1657 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1657) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1657) (by native_decide) v.1 v.2
    ((@Law1657.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1660 takes them (11 nodes). -/
def ordS8R164_Law1660 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1660. -/
theorem noS8R164_Law1660 : ∀ v : Magma.tup8R164,
    ¬ @Equation1660 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1660) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1660) (by native_decide) v.1 v.2
    ((@Law1660.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1668 takes them (11 nodes). -/
def ordS8R164_Law1668 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1668. -/
theorem noS8R164_Law1668 : ∀ v : Magma.tup8R164,
    ¬ @Equation1668 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1668) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1668) (by native_decide) v.1 v.2
    ((@Law1668.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1672 takes them (13 nodes). -/
def ordS8R164_Law1672 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1672. -/
theorem noS8R164_Law1672 : ∀ v : Magma.tup8R164,
    ¬ @Equation1672 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1672) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1672) (by native_decide) v.1 v.2
    ((@Law1672.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1721 takes them (12 nodes). -/
def ordS8R164_Law1721 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1721. -/
theorem noS8R164_Law1721 : ∀ v : Magma.tup8R164,
    ¬ @Equation1721 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1721) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1721) (by native_decide) v.1 v.2
    ((@Law1721.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1724 takes them (11 nodes). -/
def ordS8R164_Law1724 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1724. -/
theorem noS8R164_Law1724 : ∀ v : Magma.tup8R164,
    ¬ @Equation1724 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1724) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1724) (by native_decide) v.1 v.2
    ((@Law1724.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1834 takes them (17 nodes). -/
def ordS8R164_Law1834 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1834. -/
theorem noS8R164_Law1834 : ∀ v : Magma.tup8R164,
    ¬ @Equation1834 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1834) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1834) (by native_decide) v.1 v.2
    ((@Law1834.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1837 takes them (15 nodes). -/
def ordS8R164_Law1837 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1837. -/
theorem noS8R164_Law1837 : ∀ v : Magma.tup8R164,
    ¬ @Equation1837 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1837) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1837) (by native_decide) v.1 v.2
    ((@Law1837.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1847 takes them (18 nodes). -/
def ordS8R164_Law1847 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1847. -/
theorem noS8R164_Law1847 : ∀ v : Magma.tup8R164,
    ¬ @Equation1847 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1847) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1847) (by native_decide) v.1 v.2
    ((@Law1847.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1851 takes them (12 nodes). -/
def ordS8R164_Law1851 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1851. -/
theorem noS8R164_Law1851 : ∀ v : Magma.tup8R164,
    ¬ @Equation1851 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1851) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1851) (by native_decide) v.1 v.2
    ((@Law1851.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1853 takes them (16 nodes). -/
def ordS8R164_Law1853 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1853. -/
theorem noS8R164_Law1853 : ∀ v : Magma.tup8R164,
    ¬ @Equation1853 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1853) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1853) (by native_decide) v.1 v.2
    ((@Law1853.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1855 takes them (11 nodes). -/
def ordS8R164_Law1855 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1855. -/
theorem noS8R164_Law1855 : ∀ v : Magma.tup8R164,
    ¬ @Equation1855 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1855) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1855) (by native_decide) v.1 v.2
    ((@Law1855.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1860 takes them (16 nodes). -/
def ordS8R164_Law1860 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1860. -/
theorem noS8R164_Law1860 : ∀ v : Magma.tup8R164,
    ¬ @Equation1860 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1860) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law1860) (by native_decide) v.1 v.2
    ((@Law1860.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1863 takes them (13 nodes). -/
def ordS8R164_Law1863 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1863. -/
theorem noS8R164_Law1863 : ∀ v : Magma.tup8R164,
    ¬ @Equation1863 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1863) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1863) (by native_decide) v.1 v.2
    ((@Law1863.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1867 takes them (14 nodes). -/
def ordS8R164_Law1867 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1867. -/
theorem noS8R164_Law1867 : ∀ v : Magma.tup8R164,
    ¬ @Equation1867 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1867) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1867) (by native_decide) v.1 v.2
    ((@Law1867.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1871 takes them (11 nodes). -/
def ordS8R164_Law1871 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1871. -/
theorem noS8R164_Law1871 : ∀ v : Magma.tup8R164,
    ¬ @Equation1871 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1871) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1871) (by native_decide) v.1 v.2
    ((@Law1871.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1875 takes them (11 nodes). -/
def ordS8R164_Law1875 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 1875. -/
theorem noS8R164_Law1875 : ∀ v : Magma.tup8R164,
    ¬ @Equation1875 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1875) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law1875) (by native_decide) v.1 v.2
    ((@Law1875.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2050 takes them (14 nodes). -/
def ordS8R164_Law2050 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2050. -/
theorem noS8R164_Law2050 : ∀ v : Magma.tup8R164,
    ¬ @Equation2050 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2050) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2050) (by native_decide) v.1 v.2
    ((@Law2050.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2087 takes them (9 nodes). -/
def ordS8R164_Law2087 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2087. -/
theorem noS8R164_Law2087 : ∀ v : Magma.tup8R164,
    ¬ @Equation2087 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2087) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2087) (by native_decide) v.1 v.2
    ((@Law2087.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2161 takes them (9 nodes). -/
def ordS8R164_Law2161 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2161. -/
theorem noS8R164_Law2161 : ∀ v : Magma.tup8R164,
    ¬ @Equation2161 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2161) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2161) (by native_decide) v.1 v.2
    ((@Law2161.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2240 takes them (18 nodes). -/
def ordS8R164_Law2240 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2240. -/
theorem noS8R164_Law2240 : ∀ v : Magma.tup8R164,
    ¬ @Equation2240 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2240) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2240) (by native_decide) v.1 v.2
    ((@Law2240.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2243 takes them (18 nodes). -/
def ordS8R164_Law2243 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2243. -/
theorem noS8R164_Law2243 : ∀ v : Magma.tup8R164,
    ¬ @Equation2243 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2243) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2243) (by native_decide) v.1 v.2
    ((@Law2243.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2249 takes them (18 nodes). -/
def ordS8R164_Law2249 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2249. -/
theorem noS8R164_Law2249 : ∀ v : Magma.tup8R164,
    ¬ @Equation2249 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2249) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2249) (by native_decide) v.1 v.2
    ((@Law2249.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2259 takes them (16 nodes). -/
def ordS8R164_Law2259 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2259. -/
theorem noS8R164_Law2259 : ∀ v : Magma.tup8R164,
    ¬ @Equation2259 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2259) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2259) (by native_decide) v.1 v.2
    ((@Law2259.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2269 takes them (16 nodes). -/
def ordS8R164_Law2269 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2269. -/
theorem noS8R164_Law2269 : ∀ v : Magma.tup8R164,
    ¬ @Equation2269 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2269) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2269) (by native_decide) v.1 v.2
    ((@Law2269.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2273 takes them (16 nodes). -/
def ordS8R164_Law2273 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2273. -/
theorem noS8R164_Law2273 : ∀ v : Magma.tup8R164,
    ¬ @Equation2273 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2273) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2273) (by native_decide) v.1 v.2
    ((@Law2273.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2277 takes them (16 nodes). -/
def ordS8R164_Law2277 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2277. -/
theorem noS8R164_Law2277 : ∀ v : Magma.tup8R164,
    ¬ @Equation2277 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2277) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2277) (by native_decide) v.1 v.2
    ((@Law2277.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2285 takes them (16 nodes). -/
def ordS8R164_Law2285 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2285. -/
theorem noS8R164_Law2285 : ∀ v : Magma.tup8R164,
    ¬ @Equation2285 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2285) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law2285) (by native_decide) v.1 v.2
    ((@Law2285.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2296 takes them (12 nodes). -/
def ordS8R164_Law2296 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2296. -/
theorem noS8R164_Law2296 : ∀ v : Magma.tup8R164,
    ¬ @Equation2296 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2296) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2296) (by native_decide) v.1 v.2
    ((@Law2296.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2306 takes them (11 nodes). -/
def ordS8R164_Law2306 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2306. -/
theorem noS8R164_Law2306 : ∀ v : Magma.tup8R164,
    ¬ @Equation2306 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2306) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2306) (by native_decide) v.1 v.2
    ((@Law2306.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2310 takes them (11 nodes). -/
def ordS8R164_Law2310 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2310. -/
theorem noS8R164_Law2310 : ∀ v : Magma.tup8R164,
    ¬ @Equation2310 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2310) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2310) (by native_decide) v.1 v.2
    ((@Law2310.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2314 takes them (11 nodes). -/
def ordS8R164_Law2314 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2314. -/
theorem noS8R164_Law2314 : ∀ v : Magma.tup8R164,
    ¬ @Equation2314 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2314) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2314) (by native_decide) v.1 v.2
    ((@Law2314.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2322 takes them (11 nodes). -/
def ordS8R164_Law2322 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2322. -/
theorem noS8R164_Law2322 : ∀ v : Magma.tup8R164,
    ¬ @Equation2322 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2322) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law2322) (by native_decide) v.1 v.2
    ((@Law2322.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2330 takes them (13 nodes). -/
def ordS8R164_Law2330 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2330. -/
theorem noS8R164_Law2330 : ∀ v : Magma.tup8R164,
    ¬ @Equation2330 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2330) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2330) (by native_decide) v.1 v.2
    ((@Law2330.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2333 takes them (11 nodes). -/
def ordS8R164_Law2333 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2333. -/
theorem noS8R164_Law2333 : ∀ v : Magma.tup8R164,
    ¬ @Equation2333 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2333) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2333) (by native_decide) v.1 v.2
    ((@Law2333.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2351 takes them (10 nodes). -/
def ordS8R164_Law2351 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2351. -/
theorem noS8R164_Law2351 : ∀ v : Magma.tup8R164,
    ¬ @Equation2351 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2351) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2351) (by native_decide) v.1 v.2
    ((@Law2351.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2368 takes them (11 nodes). -/
def ordS8R164_Law2368 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2368. -/
theorem noS8R164_Law2368 : ∀ v : Magma.tup8R164,
    ¬ @Equation2368 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2368) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2368) (by native_decide) v.1 v.2
    ((@Law2368.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2372 takes them (11 nodes). -/
def ordS8R164_Law2372 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2372. -/
theorem noS8R164_Law2372 : ∀ v : Magma.tup8R164,
    ¬ @Equation2372 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2372) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2372) (by native_decide) v.1 v.2
    ((@Law2372.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2376 takes them (11 nodes). -/
def ordS8R164_Law2376 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2376. -/
theorem noS8R164_Law2376 : ∀ v : Magma.tup8R164,
    ¬ @Equation2376 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2376) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law2376) (by native_decide) v.1 v.2
    ((@Law2376.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2420 takes them (9 nodes). -/
def ordS8R164_Law2420 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2420. -/
theorem noS8R164_Law2420 : ∀ v : Magma.tup8R164,
    ¬ @Equation2420 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2420) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law2420) (by native_decide) v.1 v.2
    ((@Law2420.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2425 takes them (9 nodes). -/
def ordS8R164_Law2425 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2425. -/
theorem noS8R164_Law2425 : ∀ v : Magma.tup8R164,
    ¬ @Equation2425 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2425) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law2425) (by native_decide) v.1 v.2
    ((@Law2425.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2443 takes them (18 nodes). -/
def ordS8R164_Law2443 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2443. -/
theorem noS8R164_Law2443 : ∀ v : Magma.tup8R164,
    ¬ @Equation2443 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2443) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2443) (by native_decide) v.1 v.2
    ((@Law2443.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2446 takes them (18 nodes). -/
def ordS8R164_Law2446 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2446. -/
theorem noS8R164_Law2446 : ∀ v : Magma.tup8R164,
    ¬ @Equation2446 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2446) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2446) (by native_decide) v.1 v.2
    ((@Law2446.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2452 takes them (17 nodes). -/
def ordS8R164_Law2452 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2452. -/
theorem noS8R164_Law2452 : ∀ v : Magma.tup8R164,
    ¬ @Equation2452 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2452) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2452) (by native_decide) v.1 v.2
    ((@Law2452.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2456 takes them (17 nodes). -/
def ordS8R164_Law2456 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2456. -/
theorem noS8R164_Law2456 : ∀ v : Magma.tup8R164,
    ¬ @Equation2456 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2456) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2456) (by native_decide) v.1 v.2
    ((@Law2456.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2462 takes them (17 nodes). -/
def ordS8R164_Law2462 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2462. -/
theorem noS8R164_Law2462 : ∀ v : Magma.tup8R164,
    ¬ @Equation2462 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2462) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2462) (by native_decide) v.1 v.2
    ((@Law2462.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2469 takes them (17 nodes). -/
def ordS8R164_Law2469 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2469. -/
theorem noS8R164_Law2469 : ∀ v : Magma.tup8R164,
    ¬ @Equation2469 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2469) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2469) (by native_decide) v.1 v.2
    ((@Law2469.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2472 takes them (16 nodes). -/
def ordS8R164_Law2472 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2472. -/
theorem noS8R164_Law2472 : ∀ v : Magma.tup8R164,
    ¬ @Equation2472 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2472) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2472) (by native_decide) v.1 v.2
    ((@Law2472.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2476 takes them (17 nodes). -/
def ordS8R164_Law2476 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2476. -/
theorem noS8R164_Law2476 : ∀ v : Magma.tup8R164,
    ¬ @Equation2476 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2476) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2476) (by native_decide) v.1 v.2
    ((@Law2476.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2480 takes them (16 nodes). -/
def ordS8R164_Law2480 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2480. -/
theorem noS8R164_Law2480 : ∀ v : Magma.tup8R164,
    ¬ @Equation2480 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2480) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2480) (by native_decide) v.1 v.2
    ((@Law2480.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2484 takes them (16 nodes). -/
def ordS8R164_Law2484 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2484. -/
theorem noS8R164_Law2484 : ∀ v : Magma.tup8R164,
    ¬ @Equation2484 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2484) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2484) (by native_decide) v.1 v.2
    ((@Law2484.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2488 takes them (16 nodes). -/
def ordS8R164_Law2488 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2488. -/
theorem noS8R164_Law2488 : ∀ v : Magma.tup8R164,
    ¬ @Equation2488 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2488) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law2488) (by native_decide) v.1 v.2
    ((@Law2488.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2506 takes them (11 nodes). -/
def ordS8R164_Law2506 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2506. -/
theorem noS8R164_Law2506 : ∀ v : Magma.tup8R164,
    ¬ @Equation2506 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2506) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 2)
    (ord := ordS8R164_Law2506) (by native_decide) v.1 v.2
    ((@Law2506.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2517 takes them (10 nodes). -/
def ordS8R164_Law2517 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 2517. -/
theorem noS8R164_Law2517 : ∀ v : Magma.tup8R164,
    ¬ @Equation2517 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2517) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law2517) (by native_decide) v.1 v.2
    ((@Law2517.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `74` equations. -/
theorem srch8R164_refutes_2 :
    FamilyRefutes Magma.srch8R164 [
      1246, 1247, 1258, 1259, 1260, 1261, 1262, 1263, 1265, 1266, 1270, 1271, 1427, 1428, 1430,
      1631, 1634, 1640, 1644, 1650, 1657, 1660, 1668, 1672, 1721, 1724, 1834, 1837, 1847, 1851,
      1853, 1855, 1860, 1863, 1867, 1871, 1875, 2050, 2087, 2161, 2240, 2243, 2249, 2259, 2269,
      2273, 2277, 2285, 2296, 2306, 2310, 2314, 2322, 2330, 2333, 2351, 2368, 2372, 2376, 2420,
      2425, 2443, 2446, 2452, 2456, 2462, 2469, 2472, 2476, 2480, 2484, 2488, 2506, 2517
    ] :=
  ⟨noS8R164_Law1246, noS8R164_Law1247, noS8R164_Law1258, noS8R164_Law1259, noS8R164_Law1260, noS8R164_Law1261, noS8R164_Law1262, noS8R164_Law1263, noS8R164_Law1265, noS8R164_Law1266, noS8R164_Law1270, noS8R164_Law1271, noS8R164_Law1427, noS8R164_Law1428, noS8R164_Law1430, noS8R164_Law1631, noS8R164_Law1634, noS8R164_Law1640, noS8R164_Law1644, noS8R164_Law1650, noS8R164_Law1657, noS8R164_Law1660, noS8R164_Law1668, noS8R164_Law1672, noS8R164_Law1721, noS8R164_Law1724, noS8R164_Law1834, noS8R164_Law1837, noS8R164_Law1847, noS8R164_Law1851, noS8R164_Law1853, noS8R164_Law1855, noS8R164_Law1860, noS8R164_Law1863, noS8R164_Law1867, noS8R164_Law1871, noS8R164_Law1875, noS8R164_Law2050, noS8R164_Law2087, noS8R164_Law2161, noS8R164_Law2240, noS8R164_Law2243, noS8R164_Law2249, noS8R164_Law2259, noS8R164_Law2269, noS8R164_Law2273, noS8R164_Law2277, noS8R164_Law2285, noS8R164_Law2296, noS8R164_Law2306, noS8R164_Law2310, noS8R164_Law2314, noS8R164_Law2322, noS8R164_Law2330, noS8R164_Law2333, noS8R164_Law2351, noS8R164_Law2368, noS8R164_Law2372, noS8R164_Law2376, noS8R164_Law2420, noS8R164_Law2425, noS8R164_Law2443, noS8R164_Law2446, noS8R164_Law2452, noS8R164_Law2456, noS8R164_Law2462, noS8R164_Law2469, noS8R164_Law2472, noS8R164_Law2476, noS8R164_Law2480, noS8R164_Law2484, noS8R164_Law2488, noS8R164_Law2506, noS8R164_Law2517⟩
