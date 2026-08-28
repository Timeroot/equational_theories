import equational_theories.Definability.Srch_SR25

/-!
# Structural certificate targets: `Magma.srchR25` (part 2 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `14`
equations here, 3,383 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 916 takes them (273 nodes). -/
def ordSR25_Law916 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 916. -/
theorem noSR25_Law916 : ∀ v : Magma.tupR25,
    ¬ @Equation916 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law916) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law916) (by native_decide) v.1 v.2
    ((@Law916.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1036 takes them (280 nodes). -/
def ordSR25_Law1036 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1036. -/
theorem noSR25_Law1036 : ∀ v : Magma.tupR25,
    ¬ @Equation1036 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1036) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1036) (by native_decide) v.1 v.2
    ((@Law1036.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1039 takes them (202 nodes). -/
def ordSR25_Law1039 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1039. -/
theorem noSR25_Law1039 : ∀ v : Magma.tupR25,
    ¬ @Equation1039 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1039) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1039) (by native_decide) v.1 v.2
    ((@Law1039.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (259 nodes). -/
def ordSR25_Law1075 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1075. -/
theorem noSR25_Law1075 : ∀ v : Magma.tupR25,
    ¬ @Equation1075 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1082 takes them (356 nodes). -/
def ordSR25_Law1082 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1082. -/
theorem noSR25_Law1082 : ∀ v : Magma.tupR25,
    ¬ @Equation1082 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1082) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1082) (by native_decide) v.1 v.2
    ((@Law1082.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (223 nodes). -/
def ordSR25_Law1122 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1122. -/
theorem noSR25_Law1122 : ∀ v : Magma.tupR25,
    ¬ @Equation1122 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (125 nodes). -/
def ordSR25_Law1184 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1184. -/
theorem noSR25_Law1184 : ∀ v : Magma.tupR25,
    ¬ @Equation1184 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1285 takes them (324 nodes). -/
def ordSR25_Law1285 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1285. -/
theorem noSR25_Law1285 : ∀ v : Magma.tupR25,
    ¬ @Equation1285 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1285) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1285) (by native_decide) v.1 v.2
    ((@Law1285.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1312 takes them (195 nodes). -/
def ordSR25_Law1312 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1312. -/
theorem noSR25_Law1312 : ∀ v : Magma.tupR25,
    ¬ @Equation1312 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1312) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1312) (by native_decide) v.1 v.2
    ((@Law1312.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (214 nodes). -/
def ordSR25_Law1325 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1325. -/
theorem noSR25_Law1325 : ∀ v : Magma.tupR25,
    ¬ @Equation1325 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1447 takes them (154 nodes). -/
def ordSR25_Law1447 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1447. -/
theorem noSR25_Law1447 : ∀ v : Magma.tupR25,
    ¬ @Equation1447 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1447) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law1447) (by native_decide) v.1 v.2
    ((@Law1447.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1451 takes them (310 nodes). -/
def ordSR25_Law1451 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1451. -/
theorem noSR25_Law1451 : ∀ v : Magma.tupR25,
    ¬ @Equation1451 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1451) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1451) (by native_decide) v.1 v.2
    ((@Law1451.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (234 nodes). -/
def ordSR25_Law1455 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1455. -/
theorem noSR25_Law1455 : ∀ v : Magma.tupR25,
    ¬ @Equation1455 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1658 takes them (234 nodes). -/
def ordSR25_Law1658 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1658. -/
theorem noSR25_Law1658 : ∀ v : Magma.tupR25,
    ¬ @Equation1658 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1658) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law1658) (by native_decide) v.1 v.2
    ((@Law1658.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srchR25_refutes_1 :
    FamilyRefutes Magma.srchR25 [
      916, 1036, 1039, 1075, 1082, 1122, 1184, 1285, 1312, 1325, 1447, 1451, 1455, 1658
    ] :=
  ⟨noSR25_Law916, noSR25_Law1036, noSR25_Law1039, noSR25_Law1075, noSR25_Law1082, noSR25_Law1122, noSR25_Law1184, noSR25_Law1285, noSR25_Law1312, noSR25_Law1325, noSR25_Law1447, noSR25_Law1451, noSR25_Law1455, noSR25_Law1658⟩
