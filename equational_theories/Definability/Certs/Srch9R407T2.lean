import equational_theories.Definability.Srch_S9R407

/-!
# Structural certificate targets: `Magma.srch9R407` (part 3 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R407_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `17` equations here, 3,116 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R407_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3521 takes them (440 nodes). -/
def ordS9R407_Law3521 : List (Fin 7) := [2, 6, 3, 5, 4, 0, 1]

/-- No member of the class satisfies equation 3521. -/
theorem noS9R407_Law3521 : ∀ v : Magma.tup9R407,
    ¬ @Equation3521 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3529 takes them (168 nodes). -/
def ordS9R407_Law3529 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3529. -/
theorem noS9R407_Law3529 : ∀ v : Magma.tup9R407,
    ¬ @Equation3529 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3529) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3529) (by native_decide) v.1 v.2
    ((@Law3529.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3549 takes them (210 nodes). -/
def ordS9R407_Law3549 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3549. -/
theorem noS9R407_Law3549 : ∀ v : Magma.tup9R407,
    ¬ @Equation3549 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3675 takes them (31 nodes). -/
def ordS9R407_Law3675 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3675. -/
theorem noS9R407_Law3675 : ∀ v : Magma.tup9R407,
    ¬ @Equation3675 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3675) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3675) (by native_decide) v.1 v.2
    ((@Law3675.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3703 takes them (18 nodes). -/
def ordS9R407_Law3703 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3703. -/
theorem noS9R407_Law3703 : ∀ v : Magma.tup9R407,
    ¬ @Equation3703 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3703) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3703) (by native_decide) v.1 v.2
    ((@Law3703.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3714 takes them (130 nodes). -/
def ordS9R407_Law3714 : List (Fin 7) := [5, 4, 0, 1, 6, 3, 2]

/-- No member of the class satisfies equation 3714. -/
theorem noS9R407_Law3714 : ∀ v : Magma.tup9R407,
    ¬ @Equation3714 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3714) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3714) (by native_decide) v.1 v.2
    ((@Law3714.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3724 takes them (207 nodes). -/
def ordS9R407_Law3724 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3724. -/
theorem noS9R407_Law3724 : ∀ v : Magma.tup9R407,
    ¬ @Equation3724 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3724) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3724) (by native_decide) v.1 v.2
    ((@Law3724.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3726 takes them (88 nodes). -/
def ordS9R407_Law3726 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3726. -/
theorem noS9R407_Law3726 : ∀ v : Magma.tup9R407,
    ¬ @Equation3726 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3726) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3726) (by native_decide) v.1 v.2
    ((@Law3726.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3727 takes them (88 nodes). -/
def ordS9R407_Law3727 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3727. -/
theorem noS9R407_Law3727 : ∀ v : Magma.tup9R407,
    ¬ @Equation3727 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3727) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3727) (by native_decide) v.1 v.2
    ((@Law3727.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3749 takes them (207 nodes). -/
def ordS9R407_Law3749 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3749. -/
theorem noS9R407_Law3749 : ∀ v : Magma.tup9R407,
    ¬ @Equation3749 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3749) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3749) (by native_decide) v.1 v.2
    ((@Law3749.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3752 takes them (374 nodes). -/
def ordS9R407_Law3752 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3752. -/
theorem noS9R407_Law3752 : ∀ v : Magma.tup9R407,
    ¬ @Equation3752 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3752) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3752) (by native_decide) v.1 v.2
    ((@Law3752.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3769 takes them (87 nodes). -/
def ordS9R407_Law3769 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3769. -/
theorem noS9R407_Law3769 : ∀ v : Magma.tup9R407,
    ¬ @Equation3769 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3769) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3769) (by native_decide) v.1 v.2
    ((@Law3769.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3786 takes them (89 nodes). -/
def ordS9R407_Law3786 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3786. -/
theorem noS9R407_Law3786 : ∀ v : Magma.tup9R407,
    ¬ @Equation3786 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3786) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3786) (by native_decide) v.1 v.2
    ((@Law3786.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3883 takes them (102 nodes). -/
def ordS9R407_Law3883 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3883. -/
theorem noS9R407_Law3883 : ∀ v : Magma.tup9R407,
    ¬ @Equation3883 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3883) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3883) (by native_decide) v.1 v.2
    ((@Law3883.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3917 takes them (250 nodes). -/
def ordS9R407_Law3917 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3917. -/
theorem noS9R407_Law3917 : ∀ v : Magma.tup9R407,
    ¬ @Equation3917 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3931 takes them (200 nodes). -/
def ordS9R407_Law3931 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3931. -/
theorem noS9R407_Law3931 : ∀ v : Magma.tup9R407,
    ¬ @Equation3931 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3931) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3931) (by native_decide) v.1 v.2
    ((@Law3931.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3952 takes them (427 nodes). -/
def ordS9R407_Law3952 : List (Fin 7) := [2, 4, 3, 0, 5, 6, 1]

/-- No member of the class satisfies equation 3952. -/
theorem noS9R407_Law3952 : ∀ v : Magma.tup9R407,
    ¬ @Equation3952 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- No member of the class satisfies any of these `17` equations. -/
theorem srch9R407_refutes_2 :
    FamilyRefutes Magma.srch9R407 [
      3521, 3529, 3549, 3675, 3703, 3714, 3724, 3726, 3727, 3749, 3752, 3769, 3786, 3883, 3917,
      3931, 3952
    ] :=
  ⟨noS9R407_Law3521, noS9R407_Law3529, noS9R407_Law3549, noS9R407_Law3675, noS9R407_Law3703, noS9R407_Law3714, noS9R407_Law3724, noS9R407_Law3726, noS9R407_Law3727, noS9R407_Law3749, noS9R407_Law3752, noS9R407_Law3769, noS9R407_Law3786, noS9R407_Law3883, noS9R407_Law3917, noS9R407_Law3931, noS9R407_Law3952⟩
