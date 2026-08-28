import equational_theories.Definability.Srch_S8R54

/-!
# Structural certificate targets: `Magma.srch8R54` (part 10 of 14)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R54_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,684 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R54_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3414 takes them (745 nodes). -/
def ordS8R54_Law3414 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3414. -/
theorem noS8R54_Law3414 : ∀ v : Magma.tup8R54,
    ¬ @Equation3414 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3484 takes them (293 nodes). -/
def ordS8R54_Law3484 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3484. -/
theorem noS8R54_Law3484 : ∀ v : Magma.tup8R54,
    ¬ @Equation3484 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3484) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3484) (by native_decide) v.1 v.2
    ((@Law3484.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (159 nodes). -/
def ordS8R54_Law3511 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3511. -/
theorem noS8R54_Law3511 : ∀ v : Magma.tup8R54,
    ¬ @Equation3511 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3521 takes them (1097 nodes). -/
def ordS8R54_Law3521 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3521. -/
theorem noS8R54_Law3521 : ∀ v : Magma.tup8R54,
    ¬ @Equation3521 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3871 takes them (293 nodes). -/
def ordS8R54_Law3871 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3871. -/
theorem noS8R54_Law3871 : ∀ v : Magma.tup8R54,
    ¬ @Equation3871 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3871) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3871) (by native_decide) v.1 v.2
    ((@Law3871.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3952 takes them (1097 nodes). -/
def ordS8R54_Law3952 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3952. -/
theorem noS8R54_Law3952 : ∀ v : Magma.tup8R54,
    ¬ @Equation3952 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R54_refutes_9 :
    FamilyRefutes Magma.srch8R54 [
      3414, 3484, 3511, 3521, 3871, 3952
    ] :=
  ⟨noS8R54_Law3414, noS8R54_Law3484, noS8R54_Law3511, noS8R54_Law3521, noS8R54_Law3871, noS8R54_Law3952⟩
