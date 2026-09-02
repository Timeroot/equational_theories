import equational_theories.Definability.Srch_S9R1001

/-!
# Structural certificate targets: `Magma.srch9R1001`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R1001_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `10` equations here, 238 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R1001_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 452 takes them (19 nodes). -/
def ordS9R1001_Law452 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 452. -/
theorem noS9R1001_Law452 : ∀ v : Magma.tup9R1001,
    ¬ @Equation452 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law452) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law452) (by native_decide) v.1 v.2
    ((@Law452.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 655 takes them (20 nodes). -/
def ordS9R1001_Law655 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 655. -/
theorem noS9R1001_Law655 : ∀ v : Magma.tup9R1001,
    ¬ @Equation655 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law655) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law655) (by native_decide) v.1 v.2
    ((@Law655.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 861 takes them (17 nodes). -/
def ordS9R1001_Law861 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 861. -/
theorem noS9R1001_Law861 : ∀ v : Magma.tup9R1001,
    ¬ @Equation861 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law861) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law861) (by native_decide) v.1 v.2
    ((@Law861.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1061 takes them (26 nodes). -/
def ordS9R1001_Law1061 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1061. -/
theorem noS9R1001_Law1061 : ∀ v : Magma.tup9R1001,
    ¬ @Equation1061 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1061) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law1061) (by native_decide) v.1 v.2
    ((@Law1061.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2592 takes them (22 nodes). -/
def ordS9R1001_Law2592 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2592. -/
theorem noS9R1001_Law2592 : ∀ v : Magma.tup9R1001,
    ¬ @Equation2592 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2592) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law2592) (by native_decide) v.1 v.2
    ((@Law2592.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2808 takes them (16 nodes). -/
def ordS9R1001_Law2808 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2808. -/
theorem noS9R1001_Law2808 : ∀ v : Magma.tup9R1001,
    ¬ @Equation2808 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2808) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law2808) (by native_decide) v.1 v.2
    ((@Law2808.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2998 takes them (25 nodes). -/
def ordS9R1001_Law2998 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2998. -/
theorem noS9R1001_Law2998 : ∀ v : Magma.tup9R1001,
    ¬ @Equation2998 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2998) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law2998) (by native_decide) v.1 v.2
    ((@Law2998.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3201 takes them (25 nodes). -/
def ordS9R1001_Law3201 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3201. -/
theorem noS9R1001_Law3201 : ∀ v : Magma.tup9R1001,
    ¬ @Equation3201 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3201) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law3201) (by native_decide) v.1 v.2
    ((@Law3201.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (28 nodes). -/
def ordS9R1001_Law3414 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3414. -/
theorem noS9R1001_Law3414 : ∀ v : Magma.tup9R1001,
    ¬ @Equation3414 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (40 nodes). -/
def ordS9R1001_Law4135 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4135. -/
theorem noS9R1001_Law4135 : ∀ v : Magma.tup9R1001,
    ¬ @Equation4135 (Fin 9) (Magma.srch9R1001 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S9R1001.E) (tr := S9R1001.tr) (z := S9R1001.z)
    (st := S9R1001.st) (X := S9R1001.X) (envs := Magma.envsRed 9 S9R1001.E 3)
    (ord := ordS9R1001_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 9) (Magma.srch9R1001 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch9R1001_refutes_0 :
    FamilyRefutes Magma.srch9R1001 [
      452, 655, 861, 1061, 2592, 2808, 2998, 3201, 3414, 4135
    ] :=
  ⟨noS9R1001_Law452, noS9R1001_Law655, noS9R1001_Law861, noS9R1001_Law1061, noS9R1001_Law2592, noS9R1001_Law2808, noS9R1001_Law2998, noS9R1001_Law3201, noS9R1001_Law3414, noS9R1001_Law4135⟩
