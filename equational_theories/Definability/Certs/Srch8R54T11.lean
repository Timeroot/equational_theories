import equational_theories.Definability.Srch_S8R54

/-!
# Structural certificate targets: `Magma.srch8R54` (part 12 of 14)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R54_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 3,425 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R54_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4275 takes them (1129 nodes). -/
def ordS8R54_Law4275 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4275. -/
theorem noS8R54_Law4275 : ∀ v : Magma.tup8R54,
    ¬ @Equation4275 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (225 nodes). -/
def ordS8R54_Law4283 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4283. -/
theorem noS8R54_Law4283 : ∀ v : Magma.tup8R54,
    ¬ @Equation4283 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (277 nodes). -/
def ordS8R54_Law4291 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4291. -/
theorem noS8R54_Law4291 : ∀ v : Magma.tup8R54,
    ¬ @Equation4291 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4307 takes them (697 nodes). -/
def ordS8R54_Law4307 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4307. -/
theorem noS8R54_Law4307 : ∀ v : Magma.tup8R54,
    ¬ @Equation4307 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4314 takes them (1097 nodes). -/
def ordS8R54_Law4314 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4314. -/
theorem noS8R54_Law4314 : ∀ v : Magma.tup8R54,
    ¬ @Equation4314 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4314) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law4314) (by native_decide) v.1 v.2
    ((@Law4314.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch8R54_refutes_11 :
    FamilyRefutes Magma.srch8R54 [
      4275, 4283, 4291, 4307, 4314
    ] :=
  ⟨noS8R54_Law4275, noS8R54_Law4283, noS8R54_Law4291, noS8R54_Law4307, noS8R54_Law4314⟩
