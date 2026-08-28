import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 41 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `11` equations here, 3,218 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3867 takes them (1099 nodes). -/
def ordS7R12_Law3867 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3867. -/
theorem noS7R12_Law3867 : ∀ v : Magma.tup7R12,
    ¬ @Equation3867 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3867) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3867) (by native_decide) v.1 v.2
    ((@Law3867.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3869 takes them (102 nodes). -/
def ordS7R12_Law3869 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3869. -/
theorem noS7R12_Law3869 : ∀ v : Magma.tup7R12,
    ¬ @Equation3869 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3869) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3869) (by native_decide) v.1 v.2
    ((@Law3869.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3873 takes them (525 nodes). -/
def ordS7R12_Law3873 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3873. -/
theorem noS7R12_Law3873 : ∀ v : Magma.tup7R12,
    ¬ @Equation3873 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3873) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3873) (by native_decide) v.1 v.2
    ((@Law3873.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3875 takes them (109 nodes). -/
def ordS7R12_Law3875 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3875. -/
theorem noS7R12_Law3875 : ∀ v : Magma.tup7R12,
    ¬ @Equation3875 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3875) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3875) (by native_decide) v.1 v.2
    ((@Law3875.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3881 takes them (370 nodes). -/
def ordS7R12_Law3881 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3881. -/
theorem noS7R12_Law3881 : ∀ v : Magma.tup7R12,
    ¬ @Equation3881 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3881) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3881) (by native_decide) v.1 v.2
    ((@Law3881.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3882 takes them (94 nodes). -/
def ordS7R12_Law3882 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3882. -/
theorem noS7R12_Law3882 : ∀ v : Magma.tup7R12,
    ¬ @Equation3882 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3882) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3882) (by native_decide) v.1 v.2
    ((@Law3882.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3884 takes them (203 nodes). -/
def ordS7R12_Law3884 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3884. -/
theorem noS7R12_Law3884 : ∀ v : Magma.tup7R12,
    ¬ @Equation3884 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3884) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3884) (by native_decide) v.1 v.2
    ((@Law3884.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3885 takes them (98 nodes). -/
def ordS7R12_Law3885 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3885. -/
theorem noS7R12_Law3885 : ∀ v : Magma.tup7R12,
    ¬ @Equation3885 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3885) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3885) (by native_decide) v.1 v.2
    ((@Law3885.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3897 takes them (262 nodes). -/
def ordS7R12_Law3897 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3897. -/
theorem noS7R12_Law3897 : ∀ v : Magma.tup7R12,
    ¬ @Equation3897 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3897) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3897) (by native_decide) v.1 v.2
    ((@Law3897.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3898 takes them (204 nodes). -/
def ordS7R12_Law3898 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3898. -/
theorem noS7R12_Law3898 : ∀ v : Magma.tup7R12,
    ¬ @Equation3898 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3898) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3898) (by native_decide) v.1 v.2
    ((@Law3898.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3901 takes them (152 nodes). -/
def ordS7R12_Law3901 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3901. -/
theorem noS7R12_Law3901 : ∀ v : Magma.tup7R12,
    ¬ @Equation3901 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3901) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3901) (by native_decide) v.1 v.2
    ((@Law3901.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch7R12_refutes_40 :
    FamilyRefutes Magma.srch7R12 [
      3867, 3869, 3873, 3875, 3881, 3882, 3884, 3885, 3897, 3898, 3901
    ] :=
  ⟨noS7R12_Law3867, noS7R12_Law3869, noS7R12_Law3873, noS7R12_Law3875, noS7R12_Law3881, noS7R12_Law3882, noS7R12_Law3884, noS7R12_Law3885, noS7R12_Law3897, noS7R12_Law3898, noS7R12_Law3901⟩
