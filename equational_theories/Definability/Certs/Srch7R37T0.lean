import equational_theories.Definability.Srch_S7R37

/-!
# Structural certificate targets: `Magma.srch7R37`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R37_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `17` equations here, 887 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R37_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 452 takes them (51 nodes). -/
def ordS7R37_Law452 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 452. -/
theorem noS7R37_Law452 : ∀ v : Magma.tup7R37,
    ¬ @Equation452 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law452) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law452) (by native_decide) v.1 v.2
    ((@Law452.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 834 takes them (24 nodes). -/
def ordS7R37_Law834 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 834. -/
theorem noS7R37_Law834 : ∀ v : Magma.tup7R37,
    ¬ @Equation834 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law834) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law834) (by native_decide) v.1 v.2
    ((@Law834.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 837 takes them (27 nodes). -/
def ordS7R37_Law837 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 837. -/
theorem noS7R37_Law837 : ∀ v : Magma.tup7R37,
    ¬ @Equation837 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law837) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law837) (by native_decide) v.1 v.2
    ((@Law837.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1061 takes them (46 nodes). -/
def ordS7R37_Law1061 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1061. -/
theorem noS7R37_Law1061 : ∀ v : Magma.tup7R37,
    ¬ @Equation1061 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1061) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law1061) (by native_decide) v.1 v.2
    ((@Law1061.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1432 takes them (84 nodes). -/
def ordS7R37_Law1432 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1432. -/
theorem noS7R37_Law1432 : ∀ v : Magma.tup7R37,
    ¬ @Equation1432 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1432) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 2)
    (ord := ordS7R37_Law1432) (by native_decide) v.1 v.2
    ((@Law1432.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (136 nodes). -/
def ordS7R37_Law1684 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1684. -/
theorem noS7R37_Law1684 : ∀ v : Magma.tup7R37,
    ¬ @Equation1684 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 2)
    (ord := ordS7R37_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (136 nodes). -/
def ordS7R37_Law1848 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1848. -/
theorem noS7R37_Law1848 : ∀ v : Magma.tup7R37,
    ¬ @Equation1848 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 2)
    (ord := ordS7R37_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2097 takes them (84 nodes). -/
def ordS7R37_Law2097 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2097. -/
theorem noS7R37_Law2097 : ∀ v : Magma.tup7R37,
    ¬ @Equation2097 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2097) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 2)
    (ord := ordS7R37_Law2097) (by native_decide) v.1 v.2
    ((@Law2097.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2592 takes them (44 nodes). -/
def ordS7R37_Law2592 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2592. -/
theorem noS7R37_Law2592 : ∀ v : Magma.tup7R37,
    ¬ @Equation2592 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2592) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law2592) (by native_decide) v.1 v.2
    ((@Law2592.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2702 takes them (26 nodes). -/
def ordS7R37_Law2702 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2702. -/
theorem noS7R37_Law2702 : ∀ v : Magma.tup7R37,
    ¬ @Equation2702 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2702) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law2702) (by native_decide) v.1 v.2
    ((@Law2702.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2778 takes them (29 nodes). -/
def ordS7R37_Law2778 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2778. -/
theorem noS7R37_Law2778 : ∀ v : Magma.tup7R37,
    ¬ @Equation2778 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2778) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law2778) (by native_decide) v.1 v.2
    ((@Law2778.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3201 takes them (49 nodes). -/
def ordS7R37_Law3201 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3201. -/
theorem noS7R37_Law3201 : ∀ v : Magma.tup7R37,
    ¬ @Equation3201 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3201) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law3201) (by native_decide) v.1 v.2
    ((@Law3201.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4369 takes them (44 nodes). -/
def ordS7R37_Law4369 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4369. -/
theorem noS7R37_Law4369 : ∀ v : Magma.tup7R37,
    ¬ @Equation4369 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4369) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law4369) (by native_decide) v.1 v.2
    ((@Law4369.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4413 takes them (39 nodes). -/
def ordS7R37_Law4413 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4413. -/
theorem noS7R37_Law4413 : ∀ v : Magma.tup7R37,
    ¬ @Equation4413 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4413) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law4413) (by native_decide) v.1 v.2
    ((@Law4413.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4415 takes them (12 nodes). -/
def ordS7R37_Law4415 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4415. -/
theorem noS7R37_Law4415 : ∀ v : Magma.tup7R37,
    ¬ @Equation4415 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4415) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law4415) (by native_decide) v.1 v.2
    ((@Law4415.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4430 takes them (12 nodes). -/
def ordS7R37_Law4430 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4430. -/
theorem noS7R37_Law4430 : ∀ v : Magma.tup7R37,
    ¬ @Equation4430 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4430) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 4)
    (ord := ordS7R37_Law4430) (by native_decide) v.1 v.2
    ((@Law4430.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4684 takes them (44 nodes). -/
def ordS7R37_Law4684 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4684. -/
theorem noS7R37_Law4684 : ∀ v : Magma.tup7R37,
    ¬ @Equation4684 (Fin 7) (Magma.srch7R37 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4684) (E := S7R37.E) (tr := S7R37.tr) (z := S7R37.z)
    (st := S7R37.st) (X := S7R37.X) (envs := Magma.envsRed 7 S7R37.E 3)
    (ord := ordS7R37_Law4684) (by native_decide) v.1 v.2
    ((@Law4684.models_iff (Fin 7) (Magma.srch7R37 v)).mpr hv)

/-- No member of the class satisfies any of these `17` equations. -/
theorem srch7R37_refutes_0 :
    FamilyRefutes Magma.srch7R37 [
      452, 834, 837, 1061, 1432, 1684, 1848, 2097, 2592, 2702, 2778, 3201, 4369, 4413, 4415,
      4430, 4684
    ] :=
  ⟨noS7R37_Law452, noS7R37_Law834, noS7R37_Law837, noS7R37_Law1061, noS7R37_Law1432, noS7R37_Law1684, noS7R37_Law1848, noS7R37_Law2097, noS7R37_Law2592, noS7R37_Law2702, noS7R37_Law2778, noS7R37_Law3201, noS7R37_Law4369, noS7R37_Law4413, noS7R37_Law4415, noS7R37_Law4430, noS7R37_Law4684⟩
