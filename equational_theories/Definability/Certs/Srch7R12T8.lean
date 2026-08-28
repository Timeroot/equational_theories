import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 9 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,308 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1025 takes them (863 nodes). -/
def ordS7R12_Law1025 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1025. -/
theorem noS7R12_Law1025 : ∀ v : Magma.tup7R12,
    ¬ @Equation1025 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1025) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1025) (by native_decide) v.1 v.2
    ((@Law1025.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1027 takes them (115 nodes). -/
def ordS7R12_Law1027 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1027. -/
theorem noS7R12_Law1027 : ∀ v : Magma.tup7R12,
    ¬ @Equation1027 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1027) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1027) (by native_decide) v.1 v.2
    ((@Law1027.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1030 takes them (240 nodes). -/
def ordS7R12_Law1030 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1030. -/
theorem noS7R12_Law1030 : ∀ v : Magma.tup7R12,
    ¬ @Equation1030 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1030) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1030) (by native_decide) v.1 v.2
    ((@Law1030.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1031 takes them (560 nodes). -/
def ordS7R12_Law1031 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1031. -/
theorem noS7R12_Law1031 : ∀ v : Magma.tup7R12,
    ¬ @Equation1031 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1031) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1031) (by native_decide) v.1 v.2
    ((@Law1031.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1033 takes them (91 nodes). -/
def ordS7R12_Law1033 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1033. -/
theorem noS7R12_Law1033 : ∀ v : Magma.tup7R12,
    ¬ @Equation1033 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1033) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1033) (by native_decide) v.1 v.2
    ((@Law1033.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1034 takes them (70 nodes). -/
def ordS7R12_Law1034 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1034. -/
theorem noS7R12_Law1034 : ∀ v : Magma.tup7R12,
    ¬ @Equation1034 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1034) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law1034) (by native_decide) v.1 v.2
    ((@Law1034.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1041 takes them (262 nodes). -/
def ordS7R12_Law1041 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1041. -/
theorem noS7R12_Law1041 : ∀ v : Magma.tup7R12,
    ¬ @Equation1041 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1041) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1041) (by native_decide) v.1 v.2
    ((@Law1041.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1042 takes them (127 nodes). -/
def ordS7R12_Law1042 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1042. -/
theorem noS7R12_Law1042 : ∀ v : Magma.tup7R12,
    ¬ @Equation1042 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1042) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1042) (by native_decide) v.1 v.2
    ((@Law1042.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1051 takes them (263 nodes). -/
def ordS7R12_Law1051 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1051. -/
theorem noS7R12_Law1051 : ∀ v : Magma.tup7R12,
    ¬ @Equation1051 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1051) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1051) (by native_decide) v.1 v.2
    ((@Law1051.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1055 takes them (345 nodes). -/
def ordS7R12_Law1055 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1055. -/
theorem noS7R12_Law1055 : ∀ v : Magma.tup7R12,
    ¬ @Equation1055 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1055) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1055) (by native_decide) v.1 v.2
    ((@Law1055.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1056 takes them (113 nodes). -/
def ordS7R12_Law1056 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1056. -/
theorem noS7R12_Law1056 : ∀ v : Magma.tup7R12,
    ¬ @Equation1056 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1056) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1056) (by native_decide) v.1 v.2
    ((@Law1056.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1059 takes them (259 nodes). -/
def ordS7R12_Law1059 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1059. -/
theorem noS7R12_Law1059 : ∀ v : Magma.tup7R12,
    ¬ @Equation1059 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1059) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1059) (by native_decide) v.1 v.2
    ((@Law1059.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch7R12_refutes_8 :
    FamilyRefutes Magma.srch7R12 [
      1025, 1027, 1030, 1031, 1033, 1034, 1041, 1042, 1051, 1055, 1056, 1059
    ] :=
  ⟨noS7R12_Law1025, noS7R12_Law1027, noS7R12_Law1030, noS7R12_Law1031, noS7R12_Law1033, noS7R12_Law1034, noS7R12_Law1041, noS7R12_Law1042, noS7R12_Law1051, noS7R12_Law1055, noS7R12_Law1056, noS7R12_Law1059⟩
