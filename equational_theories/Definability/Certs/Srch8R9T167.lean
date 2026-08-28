import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 168 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `11`
equations here, 3,318 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3002 takes them (741 nodes). -/
def ordS8R9_Law3002 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3002. -/
theorem noS8R9_Law3002 : ∀ v : Magma.tup8R9,
    ¬ @Equation3002 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3002) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3002) (by native_decide) v.1 v.2
    ((@Law3002.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3011 takes them (741 nodes). -/
def ordS8R9_Law3011 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3011. -/
theorem noS8R9_Law3011 : ∀ v : Magma.tup8R9,
    ¬ @Equation3011 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3011) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3011) (by native_decide) v.1 v.2
    ((@Law3011.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3015 takes them (73 nodes). -/
def ordS8R9_Law3015 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3015. -/
theorem noS8R9_Law3015 : ∀ v : Magma.tup8R9,
    ¬ @Equation3015 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3015) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3015) (by native_decide) v.1 v.2
    ((@Law3015.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3019 takes them (9 nodes). -/
def ordS8R9_Law3019 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3019. -/
theorem noS8R9_Law3019 : ∀ v : Magma.tup8R9,
    ¬ @Equation3019 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3019) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3019) (by native_decide) v.1 v.2
    ((@Law3019.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3029 takes them (741 nodes). -/
def ordS8R9_Law3029 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3029. -/
theorem noS8R9_Law3029 : ∀ v : Magma.tup8R9,
    ¬ @Equation3029 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3029) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3029) (by native_decide) v.1 v.2
    ((@Law3029.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3034 takes them (13 nodes). -/
def ordS8R9_Law3034 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3034. -/
theorem noS8R9_Law3034 : ∀ v : Magma.tup8R9,
    ¬ @Equation3034 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3034) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3034) (by native_decide) v.1 v.2
    ((@Law3034.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3039 takes them (15 nodes). -/
def ordS8R9_Law3039 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3039. -/
theorem noS8R9_Law3039 : ∀ v : Magma.tup8R9,
    ¬ @Equation3039 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3039) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3039) (by native_decide) v.1 v.2
    ((@Law3039.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3044 takes them (13 nodes). -/
def ordS8R9_Law3044 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3044. -/
theorem noS8R9_Law3044 : ∀ v : Magma.tup8R9,
    ¬ @Equation3044 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3044) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law3044) (by native_decide) v.1 v.2
    ((@Law3044.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3057 takes them (123 nodes). -/
def ordS8R9_Law3057 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3057. -/
theorem noS8R9_Law3057 : ∀ v : Magma.tup8R9,
    ¬ @Equation3057 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3057) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3057) (by native_decide) v.1 v.2
    ((@Law3057.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3060 takes them (776 nodes). -/
def ordS8R9_Law3060 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3060. -/
theorem noS8R9_Law3060 : ∀ v : Magma.tup8R9,
    ¬ @Equation3060 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3060) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3060) (by native_decide) v.1 v.2
    ((@Law3060.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3062 takes them (73 nodes). -/
def ordS8R9_Law3062 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3062. -/
theorem noS8R9_Law3062 : ∀ v : Magma.tup8R9,
    ¬ @Equation3062 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3062) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3062) (by native_decide) v.1 v.2
    ((@Law3062.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch8R9_refutes_167 :
    FamilyRefutes Magma.srch8R9 [
      3002, 3011, 3015, 3019, 3029, 3034, 3039, 3044, 3057, 3060, 3062
    ] :=
  ⟨noS8R9_Law3002, noS8R9_Law3011, noS8R9_Law3015, noS8R9_Law3019, noS8R9_Law3029, noS8R9_Law3034, noS8R9_Law3039, noS8R9_Law3044, noS8R9_Law3057, noS8R9_Law3060, noS8R9_Law3062⟩
