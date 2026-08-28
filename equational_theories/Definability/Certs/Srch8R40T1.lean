import equational_theories.Definability.Srch_S8R40

/-!
# Structural certificate targets: `Magma.srch8R40` (part 2 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R40_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `16` equations here, 3,146 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R40_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3292 takes them (65 nodes). -/
def ordS8R40_Law3292 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3292. -/
theorem noS8R40_Law3292 : ∀ v : Magma.tup8R40,
    ¬ @Equation3292 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3292) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3292) (by native_decide) v.1 v.2
    ((@Law3292.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3296 takes them (63 nodes). -/
def ordS8R40_Law3296 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3296. -/
theorem noS8R40_Law3296 : ∀ v : Magma.tup8R40,
    ¬ @Equation3296 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3296) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3296) (by native_decide) v.1 v.2
    ((@Law3296.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3300 takes them (59 nodes). -/
def ordS8R40_Law3300 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3300. -/
theorem noS8R40_Law3300 : ∀ v : Magma.tup8R40,
    ¬ @Equation3300 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3300) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law3300) (by native_decide) v.1 v.2
    ((@Law3300.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3665 takes them (554 nodes). -/
def ordS8R40_Law3665 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3665. -/
theorem noS8R40_Law3665 : ∀ v : Magma.tup8R40,
    ¬ @Equation3665 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3665) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 2)
    (ord := ordS8R40_Law3665) (by native_decide) v.1 v.2
    ((@Law3665.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3666 takes them (146 nodes). -/
def ordS8R40_Law3666 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3666. -/
theorem noS8R40_Law3666 : ∀ v : Magma.tup8R40,
    ¬ @Equation3666 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3666) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3666) (by native_decide) v.1 v.2
    ((@Law3666.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3669 takes them (135 nodes). -/
def ordS8R40_Law3669 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3669. -/
theorem noS8R40_Law3669 : ∀ v : Magma.tup8R40,
    ¬ @Equation3669 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3669) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3669) (by native_decide) v.1 v.2
    ((@Law3669.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3670 takes them (171 nodes). -/
def ordS8R40_Law3670 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3670. -/
theorem noS8R40_Law3670 : ∀ v : Magma.tup8R40,
    ¬ @Equation3670 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3670) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3670) (by native_decide) v.1 v.2
    ((@Law3670.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3671 takes them (90 nodes). -/
def ordS8R40_Law3671 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3671. -/
theorem noS8R40_Law3671 : ∀ v : Magma.tup8R40,
    ¬ @Equation3671 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3671) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3671) (by native_decide) v.1 v.2
    ((@Law3671.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3672 takes them (118 nodes). -/
def ordS8R40_Law3672 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3672. -/
theorem noS8R40_Law3672 : ∀ v : Magma.tup8R40,
    ¬ @Equation3672 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3672) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3672) (by native_decide) v.1 v.2
    ((@Law3672.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3673 takes them (54 nodes). -/
def ordS8R40_Law3673 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3673. -/
theorem noS8R40_Law3673 : ∀ v : Magma.tup8R40,
    ¬ @Equation3673 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3673) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law3673) (by native_decide) v.1 v.2
    ((@Law3673.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3677 takes them (734 nodes). -/
def ordS8R40_Law3677 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3677. -/
theorem noS8R40_Law3677 : ∀ v : Magma.tup8R40,
    ¬ @Equation3677 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3677) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 2)
    (ord := ordS8R40_Law3677) (by native_decide) v.1 v.2
    ((@Law3677.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3680 takes them (288 nodes). -/
def ordS8R40_Law3680 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3680. -/
theorem noS8R40_Law3680 : ∀ v : Magma.tup8R40,
    ¬ @Equation3680 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3680) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3680) (by native_decide) v.1 v.2
    ((@Law3680.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3690 takes them (307 nodes). -/
def ordS8R40_Law3690 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3690. -/
theorem noS8R40_Law3690 : ∀ v : Magma.tup8R40,
    ¬ @Equation3690 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3690) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3690) (by native_decide) v.1 v.2
    ((@Law3690.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3698 takes them (111 nodes). -/
def ordS8R40_Law3698 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3698. -/
theorem noS8R40_Law3698 : ∀ v : Magma.tup8R40,
    ¬ @Equation3698 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3698) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3698) (by native_decide) v.1 v.2
    ((@Law3698.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3702 takes them (166 nodes). -/
def ordS8R40_Law3702 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3702. -/
theorem noS8R40_Law3702 : ∀ v : Magma.tup8R40,
    ¬ @Equation3702 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3702) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law3702) (by native_decide) v.1 v.2
    ((@Law3702.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3706 takes them (85 nodes). -/
def ordS8R40_Law3706 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3706. -/
theorem noS8R40_Law3706 : ∀ v : Magma.tup8R40,
    ¬ @Equation3706 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3706) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law3706) (by native_decide) v.1 v.2
    ((@Law3706.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch8R40_refutes_1 :
    FamilyRefutes Magma.srch8R40 [
      3292, 3296, 3300, 3665, 3666, 3669, 3670, 3671, 3672, 3673, 3677, 3680, 3690, 3698, 3702,
      3706
    ] :=
  ⟨noS8R40_Law3292, noS8R40_Law3296, noS8R40_Law3300, noS8R40_Law3665, noS8R40_Law3666, noS8R40_Law3669, noS8R40_Law3670, noS8R40_Law3671, noS8R40_Law3672, noS8R40_Law3673, noS8R40_Law3677, noS8R40_Law3680, noS8R40_Law3690, noS8R40_Law3698, noS8R40_Law3702, noS8R40_Law3706⟩
