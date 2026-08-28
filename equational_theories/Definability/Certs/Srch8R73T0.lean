import equational_theories.Definability.Srch_S8R73

/-!
# Structural certificate targets: `Magma.srch8R73`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R73_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `14` equations here, 254 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R73_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 437 takes them (9 nodes). -/
def ordS8R73_Law437 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 437. -/
theorem noS8R73_Law437 : ∀ v : Magma.tup8R73,
    ¬ @Equation437 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law437) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law437) (by native_decide) v.1 v.2
    ((@Law437.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1444 takes them (48 nodes). -/
def ordS8R73_Law1444 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1444. -/
theorem noS8R73_Law1444 : ∀ v : Magma.tup8R73,
    ¬ @Equation1444 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1655 takes them (23 nodes). -/
def ordS8R73_Law1655 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1655. -/
theorem noS8R73_Law1655 : ∀ v : Magma.tup8R73,
    ¬ @Equation1655 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1655) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law1655) (by native_decide) v.1 v.2
    ((@Law1655.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1897 takes them (23 nodes). -/
def ordS8R73_Law1897 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1897. -/
theorem noS8R73_Law1897 : ∀ v : Magma.tup8R73,
    ¬ @Equation1897 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1897) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law1897) (by native_decide) v.1 v.2
    ((@Law1897.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (48 nodes). -/
def ordS8R73_Law2053 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2053. -/
theorem noS8R73_Law2053 : ∀ v : Magma.tup8R73,
    ¬ @Equation2053 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3115 takes them (9 nodes). -/
def ordS8R73_Law3115 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3115. -/
theorem noS8R73_Law3115 : ∀ v : Magma.tup8R73,
    ¬ @Equation3115 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3115) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law3115) (by native_decide) v.1 v.2
    ((@Law3115.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (18 nodes). -/
def ordS8R73_Law3331 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3331. -/
theorem noS8R73_Law3331 : ∀ v : Magma.tup8R73,
    ¬ @Equation3331 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 3)
    (ord := ordS8R73_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3556 takes them (10 nodes). -/
def ordS8R73_Law3556 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3556. -/
theorem noS8R73_Law3556 : ∀ v : Magma.tup8R73,
    ¬ @Equation3556 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3714 takes them (9 nodes). -/
def ordS8R73_Law3714 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3714. -/
theorem noS8R73_Law3714 : ∀ v : Magma.tup8R73,
    ¬ @Equation3714 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3714) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law3714) (by native_decide) v.1 v.2
    ((@Law3714.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3752 takes them (9 nodes). -/
def ordS8R73_Law3752 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3752. -/
theorem noS8R73_Law3752 : ∀ v : Magma.tup8R73,
    ¬ @Equation3752 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3752) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law3752) (by native_decide) v.1 v.2
    ((@Law3752.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3924 takes them (10 nodes). -/
def ordS8R73_Law3924 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3924. -/
theorem noS8R73_Law3924 : ∀ v : Magma.tup8R73,
    ¬ @Equation3924 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (18 nodes). -/
def ordS8R73_Law4200 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4200. -/
theorem noS8R73_Law4200 : ∀ v : Magma.tup8R73,
    ¬ @Equation4200 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 3)
    (ord := ordS8R73_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4433 takes them (10 nodes). -/
def ordS8R73_Law4433 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4433. -/
theorem noS8R73_Law4433 : ∀ v : Magma.tup8R73,
    ¬ @Equation4433 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4433) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law4433) (by native_decide) v.1 v.2
    ((@Law4433.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4480 takes them (10 nodes). -/
def ordS8R73_Law4480 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 4480. -/
theorem noS8R73_Law4480 : ∀ v : Magma.tup8R73,
    ¬ @Equation4480 (Fin 8) (Magma.srch8R73 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4480) (E := S8R73.E) (tr := S8R73.tr) (z := S8R73.z)
    (st := S8R73.st) (X := S8R73.X) (envs := Magma.envsRed 8 S8R73.E 2)
    (ord := ordS8R73_Law4480) (by native_decide) v.1 v.2
    ((@Law4480.models_iff (Fin 8) (Magma.srch8R73 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch8R73_refutes_0 :
    FamilyRefutes Magma.srch8R73 [
      437, 1444, 1655, 1897, 2053, 3115, 3331, 3556, 3714, 3752, 3924, 4200, 4433, 4480
    ] :=
  ⟨noS8R73_Law437, noS8R73_Law1444, noS8R73_Law1655, noS8R73_Law1897, noS8R73_Law2053, noS8R73_Law3115, noS8R73_Law3331, noS8R73_Law3556, noS8R73_Law3714, noS8R73_Law3752, noS8R73_Law3924, noS8R73_Law4200, noS8R73_Law4433, noS8R73_Law4480⟩
