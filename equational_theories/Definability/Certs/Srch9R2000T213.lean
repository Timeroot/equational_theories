import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 214 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,606 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4045 takes them (607 nodes). -/
def ordS9R2000_Law4045 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4045. -/
theorem noS9R2000_Law4045 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4045 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4045) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law4045) (by native_decide) v.1 v.2
    ((@Law4045.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4050 takes them (119 nodes). -/
def ordS9R2000_Law4050 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4050. -/
theorem noS9R2000_Law4050 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4050 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4050) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law4050) (by native_decide) v.1 v.2
    ((@Law4050.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4055 takes them (119 nodes). -/
def ordS9R2000_Law4055 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4055. -/
theorem noS9R2000_Law4055 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4055 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4055) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law4055) (by native_decide) v.1 v.2
    ((@Law4055.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4060 takes them (119 nodes). -/
def ordS9R2000_Law4060 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4060. -/
theorem noS9R2000_Law4060 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4060 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4060) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 5)
    (ord := ordS9R2000_Law4060) (by native_decide) v.1 v.2
    ((@Law4060.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4122 takes them (2281 nodes). -/
def ordS9R2000_Law4122 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4122. -/
theorem noS9R2000_Law4122 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4122 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4122) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law4122) (by native_decide) v.1 v.2
    ((@Law4122.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4123 takes them (361 nodes). -/
def ordS9R2000_Law4123 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4123. -/
theorem noS9R2000_Law4123 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4123 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4123) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law4123) (by native_decide) v.1 v.2
    ((@Law4123.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch9R2000_refutes_213 :
    FamilyRefutes Magma.srch9R2000 [
      4045, 4050, 4055, 4060, 4122, 4123
    ] :=
  ⟨noS9R2000_Law4045, noS9R2000_Law4050, noS9R2000_Law4055, noS9R2000_Law4060, noS9R2000_Law4122, noS9R2000_Law4123⟩
