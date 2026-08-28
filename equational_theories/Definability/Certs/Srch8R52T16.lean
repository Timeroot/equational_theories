import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 17 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,305 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3924 takes them (418 nodes). -/
def ordS8R52_Law3924 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3924. -/
theorem noS8R52_Law3924 : ∀ v : Magma.tup8R52,
    ¬ @Equation3924 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3927 takes them (326 nodes). -/
def ordS8R52_Law3927 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3927. -/
theorem noS8R52_Law3927 : ∀ v : Magma.tup8R52,
    ¬ @Equation3927 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3927) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3927) (by native_decide) v.1 v.2
    ((@Law3927.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3952 takes them (1097 nodes). -/
def ordS8R52_Law3952 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3952. -/
theorem noS8R52_Law3952 : ∀ v : Magma.tup8R52,
    ¬ @Equation3952 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (165 nodes). -/
def ordS8R52_Law3955 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3955. -/
theorem noS8R52_Law3955 : ∀ v : Magma.tup8R52,
    ¬ @Equation3955 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3972 takes them (457 nodes). -/
def ordS8R52_Law3972 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3972. -/
theorem noS8R52_Law3972 : ∀ v : Magma.tup8R52,
    ¬ @Equation3972 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3972) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3972) (by native_decide) v.1 v.2
    ((@Law3972.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3989 takes them (417 nodes). -/
def ordS8R52_Law3989 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3989. -/
theorem noS8R52_Law3989 : ∀ v : Magma.tup8R52,
    ¬ @Equation3989 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3989) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3989) (by native_decide) v.1 v.2
    ((@Law3989.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4006 takes them (425 nodes). -/
def ordS8R52_Law4006 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4006. -/
theorem noS8R52_Law4006 : ∀ v : Magma.tup8R52,
    ¬ @Equation4006 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4006) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law4006) (by native_decide) v.1 v.2
    ((@Law4006.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch8R52_refutes_16 :
    FamilyRefutes Magma.srch8R52 [
      3924, 3927, 3952, 3955, 3972, 3989, 4006
    ] :=
  ⟨noS8R52_Law3924, noS8R52_Law3927, noS8R52_Law3952, noS8R52_Law3955, noS8R52_Law3972, noS8R52_Law3989, noS8R52_Law4006⟩
