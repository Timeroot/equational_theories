import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 6 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 3,340 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 831 takes them (131 nodes). -/
def ordS8R52_Law831 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 831. -/
theorem noS8R52_Law831 : ∀ v : Magma.tup8R52,
    ¬ @Equation831 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law831) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law831) (by native_decide) v.1 v.2
    ((@Law831.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 848 takes them (272 nodes). -/
def ordS8R52_Law848 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 848. -/
theorem noS8R52_Law848 : ∀ v : Magma.tup8R52,
    ¬ @Equation848 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law848) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law848) (by native_decide) v.1 v.2
    ((@Law848.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 856 takes them (370 nodes). -/
def ordS8R52_Law856 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 856. -/
theorem noS8R52_Law856 : ∀ v : Magma.tup8R52,
    ¬ @Equation856 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law856) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law856) (by native_decide) v.1 v.2
    ((@Law856.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 864 takes them (269 nodes). -/
def ordS8R52_Law864 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 864. -/
theorem noS8R52_Law864 : ∀ v : Magma.tup8R52,
    ¬ @Equation864 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law864) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law864) (by native_decide) v.1 v.2
    ((@Law864.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1021 takes them (396 nodes). -/
def ordS8R52_Law1021 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1021. -/
theorem noS8R52_Law1021 : ∀ v : Magma.tup8R52,
    ¬ @Equation1021 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1021) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1021) (by native_decide) v.1 v.2
    ((@Law1021.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1023 takes them (312 nodes). -/
def ordS8R52_Law1023 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1023. -/
theorem noS8R52_Law1023 : ∀ v : Magma.tup8R52,
    ¬ @Equation1023 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1023) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1023) (by native_decide) v.1 v.2
    ((@Law1023.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1024 takes them (156 nodes). -/
def ordS8R52_Law1024 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1024. -/
theorem noS8R52_Law1024 : ∀ v : Magma.tup8R52,
    ¬ @Equation1024 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1024) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1024) (by native_decide) v.1 v.2
    ((@Law1024.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1027 takes them (132 nodes). -/
def ordS8R52_Law1027 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1027. -/
theorem noS8R52_Law1027 : ∀ v : Magma.tup8R52,
    ¬ @Equation1027 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1027) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1027) (by native_decide) v.1 v.2
    ((@Law1027.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1030 takes them (131 nodes). -/
def ordS8R52_Law1030 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1030. -/
theorem noS8R52_Law1030 : ∀ v : Magma.tup8R52,
    ¬ @Equation1030 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1030) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1030) (by native_decide) v.1 v.2
    ((@Law1030.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1033 takes them (139 nodes). -/
def ordS8R52_Law1033 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1033. -/
theorem noS8R52_Law1033 : ∀ v : Magma.tup8R52,
    ¬ @Equation1033 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1033) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law1033) (by native_decide) v.1 v.2
    ((@Law1033.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1034 takes them (131 nodes). -/
def ordS8R52_Law1034 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1034. -/
theorem noS8R52_Law1034 : ∀ v : Magma.tup8R52,
    ¬ @Equation1034 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1034) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law1034) (by native_decide) v.1 v.2
    ((@Law1034.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (505 nodes). -/
def ordS8R52_Law1075 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1075. -/
theorem noS8R52_Law1075 : ∀ v : Magma.tup8R52,
    ¬ @Equation1075 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1224 takes them (396 nodes). -/
def ordS8R52_Law1224 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1224. -/
theorem noS8R52_Law1224 : ∀ v : Magma.tup8R52,
    ¬ @Equation1224 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1224) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law1224) (by native_decide) v.1 v.2
    ((@Law1224.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch8R52_refutes_5 :
    FamilyRefutes Magma.srch8R52 [
      831, 848, 856, 864, 1021, 1023, 1024, 1027, 1030, 1033, 1034, 1075, 1224
    ] :=
  ⟨noS8R52_Law831, noS8R52_Law848, noS8R52_Law856, noS8R52_Law864, noS8R52_Law1021, noS8R52_Law1023, noS8R52_Law1024, noS8R52_Law1027, noS8R52_Law1030, noS8R52_Law1033, noS8R52_Law1034, noS8R52_Law1075, noS8R52_Law1224⟩
