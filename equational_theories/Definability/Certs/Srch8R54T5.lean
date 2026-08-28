import equational_theories.Definability.Srch_S8R54

/-!
# Structural certificate targets: `Magma.srch8R54` (part 6 of 14)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R54_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,280 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R54_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1934 takes them (1145 nodes). -/
def ordS8R54_Law1934 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1934. -/
theorem noS8R54_Law1934 : ∀ v : Magma.tup8R54,
    ¬ @Equation1934 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (697 nodes). -/
def ordS8R54_Law1949 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1949. -/
theorem noS8R54_Law1949 : ∀ v : Magma.tup8R54,
    ¬ @Equation1949 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2044 takes them (293 nodes). -/
def ordS8R54_Law2044 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2044. -/
theorem noS8R54_Law2044 : ∀ v : Magma.tup8R54,
    ¬ @Equation2044 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2044) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law2044) (by native_decide) v.1 v.2
    ((@Law2044.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (1145 nodes). -/
def ordS8R54_Law2137 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2137. -/
theorem noS8R54_Law2137 : ∀ v : Magma.tup8R54,
    ¬ @Equation2137 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R54_refutes_5 :
    FamilyRefutes Magma.srch8R54 [
      1934, 1949, 2044, 2137
    ] :=
  ⟨noS8R54_Law1934, noS8R54_Law1949, noS8R54_Law2044, noS8R54_Law2137⟩
