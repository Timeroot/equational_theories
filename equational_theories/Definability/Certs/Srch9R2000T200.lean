import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 201 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `18` equations here, 2,453 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3649 takes them (54 nodes). -/
def ordS9R2000_Law3649 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3649. -/
theorem noS9R2000_Law3649 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3649 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3649) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3649) (by native_decide) v.1 v.2
    ((@Law3649.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3654 takes them (54 nodes). -/
def ordS9R2000_Law3654 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3654. -/
theorem noS9R2000_Law3654 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3654 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3654) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 5)
    (ord := ordS9R2000_Law3654) (by native_decide) v.1 v.2
    ((@Law3654.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3711 takes them (47 nodes). -/
def ordS9R2000_Law3711 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3711. -/
theorem noS9R2000_Law3711 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3711 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3711) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 2)
    (ord := ordS9R2000_Law3711) (by native_decide) v.1 v.2
    ((@Law3711.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3713 takes them (47 nodes). -/
def ordS9R2000_Law3713 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3713. -/
theorem noS9R2000_Law3713 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3713 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3713) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3713) (by native_decide) v.1 v.2
    ((@Law3713.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3717 takes them (47 nodes). -/
def ordS9R2000_Law3717 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3717. -/
theorem noS9R2000_Law3717 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3717 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3717) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3717) (by native_decide) v.1 v.2
    ((@Law3717.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3719 takes them (47 nodes). -/
def ordS9R2000_Law3719 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3719. -/
theorem noS9R2000_Law3719 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3719 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3719) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3719) (by native_decide) v.1 v.2
    ((@Law3719.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3720 takes them (47 nodes). -/
def ordS9R2000_Law3720 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3720. -/
theorem noS9R2000_Law3720 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3720 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3720) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3720) (by native_decide) v.1 v.2
    ((@Law3720.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3731 takes them (47 nodes). -/
def ordS9R2000_Law3731 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3731. -/
theorem noS9R2000_Law3731 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3731 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3731) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3731) (by native_decide) v.1 v.2
    ((@Law3731.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3733 takes them (47 nodes). -/
def ordS9R2000_Law3733 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3733. -/
theorem noS9R2000_Law3733 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3733 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3733) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3733) (by native_decide) v.1 v.2
    ((@Law3733.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3734 takes them (47 nodes). -/
def ordS9R2000_Law3734 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3734. -/
theorem noS9R2000_Law3734 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3734 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3734) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3734) (by native_decide) v.1 v.2
    ((@Law3734.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3739 takes them (46 nodes). -/
def ordS9R2000_Law3739 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3739. -/
theorem noS9R2000_Law3739 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3739 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3739) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3739) (by native_decide) v.1 v.2
    ((@Law3739.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3741 takes them (46 nodes). -/
def ordS9R2000_Law3741 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3741. -/
theorem noS9R2000_Law3741 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3741 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3741) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law3741) (by native_decide) v.1 v.2
    ((@Law3741.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3742 takes them (46 nodes). -/
def ordS9R2000_Law3742 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3742. -/
theorem noS9R2000_Law3742 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3742 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3742) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3742) (by native_decide) v.1 v.2
    ((@Law3742.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3743 takes them (42 nodes). -/
def ordS9R2000_Law3743 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3743. -/
theorem noS9R2000_Law3743 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3743 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3743) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3743) (by native_decide) v.1 v.2
    ((@Law3743.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3745 takes them (42 nodes). -/
def ordS9R2000_Law3745 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3745. -/
theorem noS9R2000_Law3745 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3745 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3745) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3745) (by native_decide) v.1 v.2
    ((@Law3745.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3746 takes them (42 nodes). -/
def ordS9R2000_Law3746 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3746. -/
theorem noS9R2000_Law3746 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3746 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3746) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law3746) (by native_decide) v.1 v.2
    ((@Law3746.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3747 takes them (42 nodes). -/
def ordS9R2000_Law3747 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3747. -/
theorem noS9R2000_Law3747 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3747 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3747) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 5)
    (ord := ordS9R2000_Law3747) (by native_decide) v.1 v.2
    ((@Law3747.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3762 takes them (1663 nodes). -/
def ordS9R2000_Law3762 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 3762. -/
theorem noS9R2000_Law3762 : ∀ v : Magma.tup9R2000,
    ¬ @Equation3762 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3762) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 2)
    (ord := ordS9R2000_Law3762) (by native_decide) v.1 v.2
    ((@Law3762.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `18` equations. -/
theorem srch9R2000_refutes_200 :
    FamilyRefutes Magma.srch9R2000 [
      3649, 3654, 3711, 3713, 3717, 3719, 3720, 3731, 3733, 3734, 3739, 3741, 3742, 3743, 3745,
      3746, 3747, 3762
    ] :=
  ⟨noS9R2000_Law3649, noS9R2000_Law3654, noS9R2000_Law3711, noS9R2000_Law3713, noS9R2000_Law3717, noS9R2000_Law3719, noS9R2000_Law3720, noS9R2000_Law3731, noS9R2000_Law3733, noS9R2000_Law3734, noS9R2000_Law3739, noS9R2000_Law3741, noS9R2000_Law3742, noS9R2000_Law3743, noS9R2000_Law3745, noS9R2000_Law3746, noS9R2000_Law3747, noS9R2000_Law3762⟩
