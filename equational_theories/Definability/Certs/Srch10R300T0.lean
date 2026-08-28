import equational_theories.Definability.Srch_S10R300

/-!
# Structural certificate targets: `Magma.srch10R300`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R300_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `23` equations here, 2,199 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R300_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 43 takes them (127 nodes). -/
def ordS10R300_Law43 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 43. -/
theorem noS10R300_Law43 : ∀ v : Magma.tup10R300,
    ¬ @Equation43 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law43) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law43) (by native_decide) v.1 v.2
    ((@Law43.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 325 takes them (92 nodes). -/
def ordS10R300_Law325 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 325. -/
theorem noS10R300_Law325 : ∀ v : Magma.tup10R300,
    ¬ @Equation325 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law325) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law325) (by native_decide) v.1 v.2
    ((@Law325.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 385 takes them (123 nodes). -/
def ordS10R300_Law385 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 385. -/
theorem noS10R300_Law385 : ∀ v : Magma.tup10R300,
    ¬ @Equation385 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law385) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law385) (by native_decide) v.1 v.2
    ((@Law385.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 834 takes them (72 nodes). -/
def ordS10R300_Law834 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 834. -/
theorem noS10R300_Law834 : ∀ v : Magma.tup10R300,
    ¬ @Equation834 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law834) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law834) (by native_decide) v.1 v.2
    ((@Law834.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 839 takes them (74 nodes). -/
def ordS10R300_Law839 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 839. -/
theorem noS10R300_Law839 : ∀ v : Magma.tup10R300,
    ¬ @Equation839 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law839) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law839) (by native_decide) v.1 v.2
    ((@Law839.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1260 takes them (95 nodes). -/
def ordS10R300_Law1260 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1260. -/
theorem noS10R300_Law1260 : ∀ v : Magma.tup10R300,
    ¬ @Equation1260 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1260) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law1260) (by native_decide) v.1 v.2
    ((@Law1260.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2306 takes them (70 nodes). -/
def ordS10R300_Law2306 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2306. -/
theorem noS10R300_Law2306 : ∀ v : Magma.tup10R300,
    ¬ @Equation2306 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2306) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law2306) (by native_decide) v.1 v.2
    ((@Law2306.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2702 takes them (88 nodes). -/
def ordS10R300_Law2702 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2702. -/
theorem noS10R300_Law2702 : ∀ v : Magma.tup10R300,
    ¬ @Equation2702 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2702) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law2702) (by native_decide) v.1 v.2
    ((@Law2702.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2774 takes them (71 nodes). -/
def ordS10R300_Law2774 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2774. -/
theorem noS10R300_Law2774 : ∀ v : Magma.tup10R300,
    ¬ @Equation2774 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2774) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law2774) (by native_decide) v.1 v.2
    ((@Law2774.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3463 takes them (46 nodes). -/
def ordS10R300_Law3463 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3463. -/
theorem noS10R300_Law3463 : ∀ v : Magma.tup10R300,
    ¬ @Equation3463 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3463) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law3463) (by native_decide) v.1 v.2
    ((@Law3463.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3521 takes them (83 nodes). -/
def ordS10R300_Law3521 : List (Fin 7) := [2, 5, 1, 0, 3, 6, 4]

/-- No member of the class satisfies equation 3521. -/
theorem noS10R300_Law3521 : ∀ v : Magma.tup10R300,
    ¬ @Equation3521 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3714 takes them (88 nodes). -/
def ordS10R300_Law3714 : List (Fin 7) := [5, 4, 0, 1, 6, 3, 2]

/-- No member of the class satisfies equation 3714. -/
theorem noS10R300_Law3714 : ∀ v : Magma.tup10R300,
    ¬ @Equation3714 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3714) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law3714) (by native_decide) v.1 v.2
    ((@Law3714.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3748 takes them (64 nodes). -/
def ordS10R300_Law3748 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3748. -/
theorem noS10R300_Law3748 : ∀ v : Magma.tup10R300,
    ¬ @Equation3748 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3748) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law3748) (by native_decide) v.1 v.2
    ((@Law3748.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3752 takes them (101 nodes). -/
def ordS10R300_Law3752 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3752. -/
theorem noS10R300_Law3752 : ∀ v : Magma.tup10R300,
    ¬ @Equation3752 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3752) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law3752) (by native_decide) v.1 v.2
    ((@Law3752.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3756 takes them (43 nodes). -/
def ordS10R300_Law3756 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3756. -/
theorem noS10R300_Law3756 : ∀ v : Magma.tup10R300,
    ¬ @Equation3756 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3756) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law3756) (by native_decide) v.1 v.2
    ((@Law3756.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3761 takes them (67 nodes). -/
def ordS10R300_Law3761 : List (Fin 7) := [6, 0, 1, 2, 4, 5, 3]

/-- No member of the class satisfies equation 3761. -/
theorem noS10R300_Law3761 : ∀ v : Magma.tup10R300,
    ¬ @Equation3761 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3761) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law3761) (by native_decide) v.1 v.2
    ((@Law3761.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3823 takes them (35 nodes). -/
def ordS10R300_Law3823 : List (Fin 7) := [2, 6, 1, 5, 4, 0, 3]

/-- No member of the class satisfies equation 3823. -/
theorem noS10R300_Law3823 : ∀ v : Magma.tup10R300,
    ¬ @Equation3823 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3823) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law3823) (by native_decide) v.1 v.2
    ((@Law3823.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3883 takes them (49 nodes). -/
def ordS10R300_Law3883 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3883. -/
theorem noS10R300_Law3883 : ∀ v : Magma.tup10R300,
    ¬ @Equation3883 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3883) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law3883) (by native_decide) v.1 v.2
    ((@Law3883.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3952 takes them (284 nodes). -/
def ordS10R300_Law3952 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3952. -/
theorem noS10R300_Law3952 : ∀ v : Magma.tup10R300,
    ¬ @Equation3952 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 2)
    (ord := ordS10R300_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4362 takes them (103 nodes). -/
def ordS10R300_Law4362 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4362. -/
theorem noS10R300_Law4362 : ∀ v : Magma.tup10R300,
    ¬ @Equation4362 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4362) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law4362) (by native_decide) v.1 v.2
    ((@Law4362.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4531 takes them (127 nodes). -/
def ordS10R300_Law4531 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4531. -/
theorem noS10R300_Law4531 : ∀ v : Magma.tup10R300,
    ¬ @Equation4531 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4531) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law4531) (by native_decide) v.1 v.2
    ((@Law4531.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4544 takes them (127 nodes). -/
def ordS10R300_Law4544 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4544. -/
theorem noS10R300_Law4544 : ∀ v : Magma.tup10R300,
    ¬ @Equation4544 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4544) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law4544) (by native_decide) v.1 v.2
    ((@Law4544.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4673 takes them (170 nodes). -/
def ordS10R300_Law4673 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4673. -/
theorem noS10R300_Law4673 : ∀ v : Magma.tup10R300,
    ¬ @Equation4673 (Fin 10) (Magma.srch10R300 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4673) (E := S10R300.E) (tr := S10R300.tr) (z := S10R300.z)
    (st := S10R300.st) (X := S10R300.X) (envs := Magma.envsRed 10 S10R300.E 3)
    (ord := ordS10R300_Law4673) (by native_decide) v.1 v.2
    ((@Law4673.models_iff (Fin 10) (Magma.srch10R300 v)).mpr hv)

/-- No member of the class satisfies any of these `23` equations. -/
theorem srch10R300_refutes_0 :
    FamilyRefutes Magma.srch10R300 [
      43, 325, 385, 834, 839, 1260, 2306, 2702, 2774, 3463, 3521, 3714, 3748, 3752, 3756, 3761,
      3823, 3883, 3952, 4362, 4531, 4544, 4673
    ] :=
  ⟨noS10R300_Law43, noS10R300_Law325, noS10R300_Law385, noS10R300_Law834, noS10R300_Law839, noS10R300_Law1260, noS10R300_Law2306, noS10R300_Law2702, noS10R300_Law2774, noS10R300_Law3463, noS10R300_Law3521, noS10R300_Law3714, noS10R300_Law3748, noS10R300_Law3752, noS10R300_Law3756, noS10R300_Law3761, noS10R300_Law3823, noS10R300_Law3883, noS10R300_Law3952, noS10R300_Law4362, noS10R300_Law4531, noS10R300_Law4544, noS10R300_Law4673⟩
