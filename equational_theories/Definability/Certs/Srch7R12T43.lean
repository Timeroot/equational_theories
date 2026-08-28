import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 44 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 2,603 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4023 takes them (446 nodes). -/
def ordS7R12_Law4023 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4023. -/
theorem noS7R12_Law4023 : ∀ v : Magma.tup7R12,
    ¬ @Equation4023 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4040 takes them (128 nodes). -/
def ordS7R12_Law4040 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4040. -/
theorem noS7R12_Law4040 : ∀ v : Magma.tup7R12,
    ¬ @Equation4040 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4040) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4040) (by native_decide) v.1 v.2
    ((@Law4040.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4072 takes them (244 nodes). -/
def ordS7R12_Law4072 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4072. -/
theorem noS7R12_Law4072 : ∀ v : Magma.tup7R12,
    ¬ @Equation4072 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4072) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4072) (by native_decide) v.1 v.2
    ((@Law4072.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4085 takes them (260 nodes). -/
def ordS7R12_Law4085 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4085. -/
theorem noS7R12_Law4085 : ∀ v : Magma.tup7R12,
    ¬ @Equation4085 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4085) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4085) (by native_decide) v.1 v.2
    ((@Law4085.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4104 takes them (262 nodes). -/
def ordS7R12_Law4104 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4104. -/
theorem noS7R12_Law4104 : ∀ v : Magma.tup7R12,
    ¬ @Equation4104 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4104) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4104) (by native_decide) v.1 v.2
    ((@Law4104.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4107 takes them (225 nodes). -/
def ordS7R12_Law4107 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4107. -/
theorem noS7R12_Law4107 : ∀ v : Magma.tup7R12,
    ¬ @Equation4107 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4107) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4107) (by native_decide) v.1 v.2
    ((@Law4107.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4112 takes them (50 nodes). -/
def ordS7R12_Law4112 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4112. -/
theorem noS7R12_Law4112 : ∀ v : Magma.tup7R12,
    ¬ @Equation4112 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4112) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4112) (by native_decide) v.1 v.2
    ((@Law4112.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4120 takes them (988 nodes). -/
def ordS7R12_Law4120 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4120. -/
theorem noS7R12_Law4120 : ∀ v : Magma.tup7R12,
    ¬ @Equation4120 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4120) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4120) (by native_decide) v.1 v.2
    ((@Law4120.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch7R12_refutes_43 :
    FamilyRefutes Magma.srch7R12 [
      4023, 4040, 4072, 4085, 4104, 4107, 4112, 4120
    ] :=
  ⟨noS7R12_Law4023, noS7R12_Law4040, noS7R12_Law4072, noS7R12_Law4085, noS7R12_Law4104, noS7R12_Law4107, noS7R12_Law4112, noS7R12_Law4120⟩
