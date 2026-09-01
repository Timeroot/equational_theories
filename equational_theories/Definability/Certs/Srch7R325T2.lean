import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 3 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,341 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3886 takes them (10 nodes). -/
def ordS7R325_Law3886 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3886. -/
theorem noS7R325_Law3886 : ∀ v : Magma.tup7R325,
    ¬ @Equation3886 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3886) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3886) (by native_decide) v.1 v.2
    ((@Law3886.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3900 takes them (10 nodes). -/
def ordS7R325_Law3900 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3900. -/
theorem noS7R325_Law3900 : ∀ v : Magma.tup7R325,
    ¬ @Equation3900 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3900) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3900) (by native_decide) v.1 v.2
    ((@Law3900.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3909 takes them (58 nodes). -/
def ordS7R325_Law3909 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3909. -/
theorem noS7R325_Law3909 : ∀ v : Magma.tup7R325,
    ¬ @Equation3909 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3909) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law3909) (by native_decide) v.1 v.2
    ((@Law3909.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3913 takes them (10 nodes). -/
def ordS7R325_Law3913 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3913. -/
theorem noS7R325_Law3913 : ∀ v : Magma.tup7R325,
    ¬ @Equation3913 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3913) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law3913) (by native_decide) v.1 v.2
    ((@Law3913.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3951 takes them (2200 nodes). -/
def ordS7R325_Law3951 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3951. -/
theorem noS7R325_Law3951 : ∀ v : Magma.tup7R325,
    ¬ @Equation3951 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3951) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 2)
    (ord := ordS7R325_Law3951) (by native_decide) v.1 v.2
    ((@Law3951.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3979 takes them (53 nodes). -/
def ordS7R325_Law3979 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3979. -/
theorem noS7R325_Law3979 : ∀ v : Magma.tup7R325,
    ¬ @Equation3979 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3979) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3979) (by native_decide) v.1 v.2
    ((@Law3979.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (872 nodes). -/
def ordS7R325_Law3997 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 3997. -/
theorem noS7R325_Law3997 : ∀ v : Magma.tup7R325,
    ¬ @Equation3997 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4079 takes them (40 nodes). -/
def ordS7R325_Law4079 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4079. -/
theorem noS7R325_Law4079 : ∀ v : Magma.tup7R325,
    ¬ @Equation4079 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4079) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4079) (by native_decide) v.1 v.2
    ((@Law4079.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4089 takes them (10 nodes). -/
def ordS7R325_Law4089 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4089. -/
theorem noS7R325_Law4089 : ∀ v : Magma.tup7R325,
    ¬ @Equation4089 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4089) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4089) (by native_decide) v.1 v.2
    ((@Law4089.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4103 takes them (10 nodes). -/
def ordS7R325_Law4103 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4103. -/
theorem noS7R325_Law4103 : ∀ v : Magma.tup7R325,
    ¬ @Equation4103 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4103) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4103) (by native_decide) v.1 v.2
    ((@Law4103.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4112 takes them (58 nodes). -/
def ordS7R325_Law4112 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4112. -/
theorem noS7R325_Law4112 : ∀ v : Magma.tup7R325,
    ¬ @Equation4112 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4112) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4112) (by native_decide) v.1 v.2
    ((@Law4112.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4116 takes them (10 nodes). -/
def ordS7R325_Law4116 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4116. -/
theorem noS7R325_Law4116 : ∀ v : Magma.tup7R325,
    ¬ @Equation4116 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4116) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4116) (by native_decide) v.1 v.2
    ((@Law4116.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch7R325_refutes_2 :
    FamilyRefutes Magma.srch7R325 [
      3886, 3900, 3909, 3913, 3951, 3979, 3997, 4079, 4089, 4103, 4112, 4116
    ] :=
  ⟨noS7R325_Law3886, noS7R325_Law3900, noS7R325_Law3909, noS7R325_Law3913, noS7R325_Law3951, noS7R325_Law3979, noS7R325_Law3997, noS7R325_Law4079, noS7R325_Law4089, noS7R325_Law4103, noS7R325_Law4112, noS7R325_Law4116⟩
