import equational_theories.Definability.Srch_S8R13

/-!
# Structural certificate targets: `Magma.srch8R13` (part 80 of 85)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 2,883 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3946 takes them (494 nodes). -/
def ordS8R13_Law3946 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3946. -/
theorem noS8R13_Law3946 : ∀ v : Magma.tup8R13,
    ¬ @Equation3946 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3946) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 4)
    (ord := ordS8R13_Law3946) (by native_decide) v.1 v.2
    ((@Law3946.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3948 takes them (388 nodes). -/
def ordS8R13_Law3948 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3948. -/
theorem noS8R13_Law3948 : ∀ v : Magma.tup8R13,
    ¬ @Equation3948 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3948) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 4)
    (ord := ordS8R13_Law3948) (by native_decide) v.1 v.2
    ((@Law3948.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3949 takes them (397 nodes). -/
def ordS8R13_Law3949 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3949. -/
theorem noS8R13_Law3949 : ∀ v : Magma.tup8R13,
    ¬ @Equation3949 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3949) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 4)
    (ord := ordS8R13_Law3949) (by native_decide) v.1 v.2
    ((@Law3949.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3950 takes them (387 nodes). -/
def ordS8R13_Law3950 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3950. -/
theorem noS8R13_Law3950 : ∀ v : Magma.tup8R13,
    ¬ @Equation3950 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3950) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 5)
    (ord := ordS8R13_Law3950) (by native_decide) v.1 v.2
    ((@Law3950.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4384 takes them (434 nodes). -/
def ordS8R13_Law4384 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4384. -/
theorem noS8R13_Law4384 : ∀ v : Magma.tup8R13,
    ¬ @Equation4384 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4384) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law4384) (by native_decide) v.1 v.2
    ((@Law4384.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4404 takes them (393 nodes). -/
def ordS8R13_Law4404 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4404. -/
theorem noS8R13_Law4404 : ∀ v : Magma.tup8R13,
    ¬ @Equation4404 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4404) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 4)
    (ord := ordS8R13_Law4404) (by native_decide) v.1 v.2
    ((@Law4404.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4441 takes them (390 nodes). -/
def ordS8R13_Law4441 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4441. -/
theorem noS8R13_Law4441 : ∀ v : Magma.tup8R13,
    ¬ @Equation4441 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4441) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 4)
    (ord := ordS8R13_Law4441) (by native_decide) v.1 v.2
    ((@Law4441.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch8R13_refutes_79 :
    FamilyRefutes Magma.srch8R13 [
      3946, 3948, 3949, 3950, 4384, 4404, 4441
    ] :=
  ⟨noS8R13_Law3946, noS8R13_Law3948, noS8R13_Law3949, noS8R13_Law3950, noS8R13_Law4384, noS8R13_Law4404, noS8R13_Law4441⟩
