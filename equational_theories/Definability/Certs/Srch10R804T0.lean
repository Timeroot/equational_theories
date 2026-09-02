import equational_theories.Definability.Srch_S10R804

/-!
# Structural certificate targets: `Magma.srch10R804`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R804_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 2,784 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R804_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 325 takes them (383 nodes). -/
def ordS10R804_Law325 : List (Fin 8) := [7, 0, 4, 2, 1, 6, 5, 3]

/-- No member of the class satisfies equation 325. -/
theorem noS10R804_Law325 : ∀ v : Magma.tup10R804,
    ¬ @Equation325 (Fin 10) (Magma.srch10R804 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law325) (E := S10R804.E) (tr := S10R804.tr) (z := S10R804.z)
    (st := S10R804.st) (X := S10R804.X) (envs := Magma.envsRed 10 S10R804.E 2)
    (ord := ordS10R804_Law325) (by native_decide) v.1 v.2
    ((@Law325.models_iff (Fin 10) (Magma.srch10R804 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 385 takes them (435 nodes). -/
def ordS10R804_Law385 : List (Fin 8) := [3, 0, 4, 6, 7, 1, 5, 2]

/-- No member of the class satisfies equation 385. -/
theorem noS10R804_Law385 : ∀ v : Magma.tup10R804,
    ¬ @Equation385 (Fin 10) (Magma.srch10R804 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law385) (E := S10R804.E) (tr := S10R804.tr) (z := S10R804.z)
    (st := S10R804.st) (X := S10R804.X) (envs := Magma.envsRed 10 S10R804.E 2)
    (ord := ordS10R804_Law385) (by native_decide) v.1 v.2
    ((@Law385.models_iff (Fin 10) (Magma.srch10R804 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3714 takes them (289 nodes). -/
def ordS10R804_Law3714 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3714. -/
theorem noS10R804_Law3714 : ∀ v : Magma.tup10R804,
    ¬ @Equation3714 (Fin 10) (Magma.srch10R804 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3714) (E := S10R804.E) (tr := S10R804.tr) (z := S10R804.z)
    (st := S10R804.st) (X := S10R804.X) (envs := Magma.envsRed 10 S10R804.E 2)
    (ord := ordS10R804_Law3714) (by native_decide) v.1 v.2
    ((@Law3714.models_iff (Fin 10) (Magma.srch10R804 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3752 takes them (391 nodes). -/
def ordS10R804_Law3752 : List (Fin 8) := [3, 7, 2, 6, 0, 4, 5, 1]

/-- No member of the class satisfies equation 3752. -/
theorem noS10R804_Law3752 : ∀ v : Magma.tup10R804,
    ¬ @Equation3752 (Fin 10) (Magma.srch10R804 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3752) (E := S10R804.E) (tr := S10R804.tr) (z := S10R804.z)
    (st := S10R804.st) (X := S10R804.X) (envs := Magma.envsRed 10 S10R804.E 2)
    (ord := ordS10R804_Law3752) (by native_decide) v.1 v.2
    ((@Law3752.models_iff (Fin 10) (Magma.srch10R804 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4406 takes them (374 nodes). -/
def ordS10R804_Law4406 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4406. -/
theorem noS10R804_Law4406 : ∀ v : Magma.tup10R804,
    ¬ @Equation4406 (Fin 10) (Magma.srch10R804 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4406) (E := S10R804.E) (tr := S10R804.tr) (z := S10R804.z)
    (st := S10R804.st) (X := S10R804.X) (envs := Magma.envsRed 10 S10R804.E 2)
    (ord := ordS10R804_Law4406) (by native_decide) v.1 v.2
    ((@Law4406.models_iff (Fin 10) (Magma.srch10R804 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4433 takes them (359 nodes). -/
def ordS10R804_Law4433 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4433. -/
theorem noS10R804_Law4433 : ∀ v : Magma.tup10R804,
    ¬ @Equation4433 (Fin 10) (Magma.srch10R804 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4433) (E := S10R804.E) (tr := S10R804.tr) (z := S10R804.z)
    (st := S10R804.st) (X := S10R804.X) (envs := Magma.envsRed 10 S10R804.E 2)
    (ord := ordS10R804_Law4433) (by native_decide) v.1 v.2
    ((@Law4433.models_iff (Fin 10) (Magma.srch10R804 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4436 takes them (374 nodes). -/
def ordS10R804_Law4436 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4436. -/
theorem noS10R804_Law4436 : ∀ v : Magma.tup10R804,
    ¬ @Equation4436 (Fin 10) (Magma.srch10R804 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4436) (E := S10R804.E) (tr := S10R804.tr) (z := S10R804.z)
    (st := S10R804.st) (X := S10R804.X) (envs := Magma.envsRed 10 S10R804.E 2)
    (ord := ordS10R804_Law4436) (by native_decide) v.1 v.2
    ((@Law4436.models_iff (Fin 10) (Magma.srch10R804 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4480 takes them (179 nodes). -/
def ordS10R804_Law4480 : List (Fin 8) := [0, 6, 2, 4, 5, 7, 3, 1]

/-- No member of the class satisfies equation 4480. -/
theorem noS10R804_Law4480 : ∀ v : Magma.tup10R804,
    ¬ @Equation4480 (Fin 10) (Magma.srch10R804 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4480) (E := S10R804.E) (tr := S10R804.tr) (z := S10R804.z)
    (st := S10R804.st) (X := S10R804.X) (envs := Magma.envsRed 10 S10R804.E 2)
    (ord := ordS10R804_Law4480) (by native_decide) v.1 v.2
    ((@Law4480.models_iff (Fin 10) (Magma.srch10R804 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch10R804_refutes_0 :
    FamilyRefutes Magma.srch10R804 [
      325, 385, 3714, 3752, 4406, 4433, 4436, 4480
    ] :=
  ⟨noS10R804_Law325, noS10R804_Law385, noS10R804_Law3714, noS10R804_Law3752, noS10R804_Law4406, noS10R804_Law4433, noS10R804_Law4436, noS10R804_Law4480⟩
