import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 2 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 3,446 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3534 takes them (872 nodes). -/
def ordS7R325_Law3534 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3534. -/
theorem noS7R325_Law3534 : ∀ v : Magma.tup7R325,
    ¬ @Equation3534 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3558 takes them (2200 nodes). -/
def ordS7R325_Law3558 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3558. -/
theorem noS7R325_Law3558 : ∀ v : Magma.tup7R325,
    ¬ @Equation3558 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3558) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 2)
    (ord := ordS7R325_Law3558) (by native_decide) v.1 v.2
    ((@Law3558.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3573 takes them (53 nodes). -/
def ordS7R325_Law3573 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3573. -/
theorem noS7R325_Law3573 : ∀ v : Magma.tup7R325,
    ¬ @Equation3573 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3573) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3573) (by native_decide) v.1 v.2
    ((@Law3573.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3673 takes them (22 nodes). -/
def ordS7R325_Law3673 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3673. -/
theorem noS7R325_Law3673 : ∀ v : Magma.tup7R325,
    ¬ @Equation3673 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3673) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3673) (by native_decide) v.1 v.2
    ((@Law3673.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3683 takes them (10 nodes). -/
def ordS7R325_Law3683 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3683. -/
theorem noS7R325_Law3683 : ∀ v : Magma.tup7R325,
    ¬ @Equation3683 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3683) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3683) (by native_decide) v.1 v.2
    ((@Law3683.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3697 takes them (10 nodes). -/
def ordS7R325_Law3697 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3697. -/
theorem noS7R325_Law3697 : ∀ v : Magma.tup7R325,
    ¬ @Equation3697 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3697) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3697) (by native_decide) v.1 v.2
    ((@Law3697.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3706 takes them (28 nodes). -/
def ordS7R325_Law3706 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3706. -/
theorem noS7R325_Law3706 : ∀ v : Magma.tup7R325,
    ¬ @Equation3706 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3706) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3706) (by native_decide) v.1 v.2
    ((@Law3706.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3710 takes them (10 nodes). -/
def ordS7R325_Law3710 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3710. -/
theorem noS7R325_Law3710 : ∀ v : Magma.tup7R325,
    ¬ @Equation3710 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3710) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law3710) (by native_decide) v.1 v.2
    ((@Law3710.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3727 takes them (92 nodes). -/
def ordS7R325_Law3727 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3727. -/
theorem noS7R325_Law3727 : ∀ v : Magma.tup7R325,
    ¬ @Equation3727 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3727) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3727) (by native_decide) v.1 v.2
    ((@Law3727.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3730 takes them (17 nodes). -/
def ordS7R325_Law3730 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3730. -/
theorem noS7R325_Law3730 : ∀ v : Magma.tup7R325,
    ¬ @Equation3730 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3730) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3730) (by native_decide) v.1 v.2
    ((@Law3730.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3769 takes them (92 nodes). -/
def ordS7R325_Law3769 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3769. -/
theorem noS7R325_Law3769 : ∀ v : Magma.tup7R325,
    ¬ @Equation3769 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3769) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3769) (by native_decide) v.1 v.2
    ((@Law3769.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3837 takes them (18 nodes). -/
def ordS7R325_Law3837 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3837. -/
theorem noS7R325_Law3837 : ∀ v : Magma.tup7R325,
    ¬ @Equation3837 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3837) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3837) (by native_decide) v.1 v.2
    ((@Law3837.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3876 takes them (22 nodes). -/
def ordS7R325_Law3876 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3876. -/
theorem noS7R325_Law3876 : ∀ v : Magma.tup7R325,
    ¬ @Equation3876 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3876) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3876) (by native_decide) v.1 v.2
    ((@Law3876.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch7R325_refutes_1 :
    FamilyRefutes Magma.srch7R325 [
      3534, 3558, 3573, 3673, 3683, 3697, 3706, 3710, 3727, 3730, 3769, 3837, 3876
    ] :=
  ⟨noS7R325_Law3534, noS7R325_Law3558, noS7R325_Law3573, noS7R325_Law3673, noS7R325_Law3683, noS7R325_Law3697, noS7R325_Law3706, noS7R325_Law3710, noS7R325_Law3727, noS7R325_Law3730, noS7R325_Law3769, noS7R325_Law3837, noS7R325_Law3876⟩
