import equational_theories.Definability.Srch_S16R308

/-!
# Structural certificate targets: `Magma.srch16R308`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S16R308_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 84 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S16R308_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 427 takes them (13 nodes). -/
def ordS16R308_Law427 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 427. -/
theorem noS16R308_Law427 : ∀ v : Magma.tup16R308,
    ¬ @Equation427 (Fin 16) (Magma.srch16R308 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law427) (E := S16R308.E) (tr := S16R308.tr) (z := S16R308.z)
    (st := S16R308.st) (X := S16R308.X) (envs := Magma.envsRed 16 S16R308.E 2)
    (ord := ordS16R308_Law427) (by native_decide) v.1 v.2
    ((@Law427.models_iff (Fin 16) (Magma.srch16R308 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1046 takes them (7 nodes). -/
def ordS16R308_Law1046 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1046. -/
theorem noS16R308_Law1046 : ∀ v : Magma.tup16R308,
    ¬ @Equation1046 (Fin 16) (Magma.srch16R308 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1046) (E := S16R308.E) (tr := S16R308.tr) (z := S16R308.z)
    (st := S16R308.st) (X := S16R308.X) (envs := Magma.envsRed 16 S16R308.E 2)
    (ord := ordS16R308_Law1046) (by native_decide) v.1 v.2
    ((@Law1046.models_iff (Fin 16) (Magma.srch16R308 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1239 takes them (13 nodes). -/
def ordS16R308_Law1239 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 1239. -/
theorem noS16R308_Law1239 : ∀ v : Magma.tup16R308,
    ¬ @Equation1239 (Fin 16) (Magma.srch16R308 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1239) (E := S16R308.E) (tr := S16R308.tr) (z := S16R308.z)
    (st := S16R308.st) (X := S16R308.X) (envs := Magma.envsRed 16 S16R308.E 2)
    (ord := ordS16R308_Law1239) (by native_decide) v.1 v.2
    ((@Law1239.models_iff (Fin 16) (Magma.srch16R308 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2293 takes them (13 nodes). -/
def ordS16R308_Law2293 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2293. -/
theorem noS16R308_Law2293 : ∀ v : Magma.tup16R308,
    ¬ @Equation2293 (Fin 16) (Magma.srch16R308 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2293) (E := S16R308.E) (tr := S16R308.tr) (z := S16R308.z)
    (st := S16R308.st) (X := S16R308.X) (envs := Magma.envsRed 16 S16R308.E 2)
    (ord := ordS16R308_Law2293) (by native_decide) v.1 v.2
    ((@Law2293.models_iff (Fin 16) (Magma.srch16R308 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2506 takes them (7 nodes). -/
def ordS16R308_Law2506 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 2506. -/
theorem noS16R308_Law2506 : ∀ v : Magma.tup16R308,
    ¬ @Equation2506 (Fin 16) (Magma.srch16R308 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2506) (E := S16R308.E) (tr := S16R308.tr) (z := S16R308.z)
    (st := S16R308.st) (X := S16R308.X) (envs := Magma.envsRed 16 S16R308.E 2)
    (ord := ordS16R308_Law2506) (by native_decide) v.1 v.2
    ((@Law2506.models_iff (Fin 16) (Magma.srch16R308 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3105 takes them (13 nodes). -/
def ordS16R308_Law3105 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3105. -/
theorem noS16R308_Law3105 : ∀ v : Magma.tup16R308,
    ¬ @Equation3105 (Fin 16) (Magma.srch16R308 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3105) (E := S16R308.E) (tr := S16R308.tr) (z := S16R308.z)
    (st := S16R308.st) (X := S16R308.X) (envs := Magma.envsRed 16 S16R308.E 2)
    (ord := ordS16R308_Law3105) (by native_decide) v.1 v.2
    ((@Law3105.models_iff (Fin 16) (Magma.srch16R308 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (9 nodes). -/
def ordS16R308_Law3526 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3526. -/
theorem noS16R308_Law3526 : ∀ v : Magma.tup16R308,
    ¬ @Equation3526 (Fin 16) (Magma.srch16R308 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S16R308.E) (tr := S16R308.tr) (z := S16R308.z)
    (st := S16R308.st) (X := S16R308.X) (envs := Magma.envsRed 16 S16R308.E 3)
    (ord := ordS16R308_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 16) (Magma.srch16R308 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (9 nodes). -/
def ordS16R308_Law4023 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4023. -/
theorem noS16R308_Law4023 : ∀ v : Magma.tup16R308,
    ¬ @Equation4023 (Fin 16) (Magma.srch16R308 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S16R308.E) (tr := S16R308.tr) (z := S16R308.z)
    (st := S16R308.st) (X := S16R308.X) (envs := Magma.envsRed 16 S16R308.E 3)
    (ord := ordS16R308_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 16) (Magma.srch16R308 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch16R308_refutes_0 :
    FamilyRefutes Magma.srch16R308 [
      427, 1046, 1239, 2293, 2506, 3105, 3526, 4023
    ] :=
  ⟨noS16R308_Law427, noS16R308_Law1046, noS16R308_Law1239, noS16R308_Law2293, noS16R308_Law2506, noS16R308_Law3105, noS16R308_Law3526, noS16R308_Law4023⟩
