import equational_theories.Definability.Srch_S8R54

/-!
# Structural certificate targets: `Magma.srch8R54` (part 3 of 14)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R54_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,268 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R54_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1075 takes them (761 nodes). -/
def ordS8R54_Law1075 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1075. -/
theorem noS8R54_Law1075 : ∀ v : Magma.tup8R54,
    ¬ @Equation1075 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (1145 nodes). -/
def ordS8R54_Law1122 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1122. -/
theorem noS8R54_Law1122 : ∀ v : Magma.tup8R54,
    ¬ @Equation1122 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (697 nodes). -/
def ordS8R54_Law1184 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1184. -/
theorem noS8R54_Law1184 : ∀ v : Magma.tup8R54,
    ¬ @Equation1184 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (665 nodes). -/
def ordS8R54_Law1278 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1278. -/
theorem noS8R54_Law1278 : ∀ v : Magma.tup8R54,
    ¬ @Equation1278 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R54_refutes_2 :
    FamilyRefutes Magma.srch8R54 [
      1075, 1122, 1184, 1278
    ] :=
  ⟨noS8R54_Law1075, noS8R54_Law1122, noS8R54_Law1184, noS8R54_Law1278⟩
