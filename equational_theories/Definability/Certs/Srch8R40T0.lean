import equational_theories.Definability.Srch_S8R40

/-!
# Structural certificate targets: `Magma.srch8R40` (part 1 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R40_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 3,605 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R40_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 318 takes them (52 nodes). -/
def ordS8R40_Law318 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 318. -/
theorem noS8R40_Law318 : ∀ v : Magma.tup8R40,
    ¬ @Equation318 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law318) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law318) (by native_decide) v.1 v.2
    ((@Law318.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 363 takes them (39 nodes). -/
def ordS8R40_Law363 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 363. -/
theorem noS8R40_Law363 : ∀ v : Magma.tup8R40,
    ¬ @Equation363 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law363) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law363) (by native_decide) v.1 v.2
    ((@Law363.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1312 takes them (277 nodes). -/
def ordS8R40_Law1312 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1312. -/
theorem noS8R40_Law1312 : ∀ v : Magma.tup8R40,
    ¬ @Equation1312 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1312) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 2)
    (ord := ordS8R40_Law1312) (by native_decide) v.1 v.2
    ((@Law1312.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1444 takes them (1324 nodes). -/
def ordS8R40_Law1444 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1444. -/
theorem noS8R40_Law1444 : ∀ v : Magma.tup8R40,
    ¬ @Equation1444 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 2)
    (ord := ordS8R40_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (1401 nodes). -/
def ordS8R40_Law2053 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2053. -/
theorem noS8R40_Law2053 : ∀ v : Magma.tup8R40,
    ¬ @Equation2053 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 2)
    (ord := ordS8R40_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2241 takes them (317 nodes). -/
def ordS8R40_Law2241 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2241. -/
theorem noS8R40_Law2241 : ∀ v : Magma.tup8R40,
    ¬ @Equation2241 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2241) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 2)
    (ord := ordS8R40_Law2241) (by native_decide) v.1 v.2
    ((@Law2241.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3274 takes them (129 nodes). -/
def ordS8R40_Law3274 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3274. -/
theorem noS8R40_Law3274 : ∀ v : Magma.tup8R40,
    ¬ @Equation3274 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3274) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3274) (by native_decide) v.1 v.2
    ((@Law3274.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3284 takes them (66 nodes). -/
def ordS8R40_Law3284 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3284. -/
theorem noS8R40_Law3284 : ∀ v : Magma.tup8R40,
    ¬ @Equation3284 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3284) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3284) (by native_decide) v.1 v.2
    ((@Law3284.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch8R40_refutes_0 :
    FamilyRefutes Magma.srch8R40 [
      318, 363, 1312, 1444, 2053, 2241, 3274, 3284
    ] :=
  ⟨noS8R40_Law318, noS8R40_Law363, noS8R40_Law1312, noS8R40_Law1444, noS8R40_Law2053, noS8R40_Law2241, noS8R40_Law3274, noS8R40_Law3284⟩
