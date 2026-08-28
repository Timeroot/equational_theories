import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 43 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `10` equations here, 3,523 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3952 takes them (748 nodes). -/
def ordS7R12_Law3952 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3952. -/
theorem noS7R12_Law3952 : ∀ v : Magma.tup7R12,
    ¬ @Equation3952 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3952) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3952) (by native_decide) v.1 v.2
    ((@Law3952.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3954 takes them (147 nodes). -/
def ordS7R12_Law3954 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3954. -/
theorem noS7R12_Law3954 : ∀ v : Magma.tup7R12,
    ¬ @Equation3954 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3954) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3954) (by native_decide) v.1 v.2
    ((@Law3954.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3962 takes them (980 nodes). -/
def ordS7R12_Law3962 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3962. -/
theorem noS7R12_Law3962 : ∀ v : Magma.tup7R12,
    ¬ @Equation3962 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3962) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3962) (by native_decide) v.1 v.2
    ((@Law3962.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3964 takes them (483 nodes). -/
def ordS7R12_Law3964 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3964. -/
theorem noS7R12_Law3964 : ∀ v : Magma.tup7R12,
    ¬ @Equation3964 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3964) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3964) (by native_decide) v.1 v.2
    ((@Law3964.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3972 takes them (152 nodes). -/
def ordS7R12_Law3972 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3972. -/
theorem noS7R12_Law3972 : ∀ v : Magma.tup7R12,
    ¬ @Equation3972 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3972) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3972) (by native_decide) v.1 v.2
    ((@Law3972.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3979 takes them (236 nodes). -/
def ordS7R12_Law3979 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3979. -/
theorem noS7R12_Law3979 : ∀ v : Magma.tup7R12,
    ¬ @Equation3979 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3979) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3979) (by native_decide) v.1 v.2
    ((@Law3979.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3989 takes them (316 nodes). -/
def ordS7R12_Law3989 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3989. -/
theorem noS7R12_Law3989 : ∀ v : Magma.tup7R12,
    ¬ @Equation3989 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3989) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3989) (by native_decide) v.1 v.2
    ((@Law3989.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3993 takes them (64 nodes). -/
def ordS7R12_Law3993 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3993. -/
theorem noS7R12_Law3993 : ∀ v : Magma.tup7R12,
    ¬ @Equation3993 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3993) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3993) (by native_decide) v.1 v.2
    ((@Law3993.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (215 nodes). -/
def ordS7R12_Law3997 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3997. -/
theorem noS7R12_Law3997 : ∀ v : Magma.tup7R12,
    ¬ @Equation3997 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4006 takes them (182 nodes). -/
def ordS7R12_Law4006 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4006. -/
theorem noS7R12_Law4006 : ∀ v : Magma.tup7R12,
    ¬ @Equation4006 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4006) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4006) (by native_decide) v.1 v.2
    ((@Law4006.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch7R12_refutes_42 :
    FamilyRefutes Magma.srch7R12 [
      3952, 3954, 3962, 3964, 3972, 3979, 3989, 3993, 3997, 4006
    ] :=
  ⟨noS7R12_Law3952, noS7R12_Law3954, noS7R12_Law3962, noS7R12_Law3964, noS7R12_Law3972, noS7R12_Law3979, noS7R12_Law3989, noS7R12_Law3993, noS7R12_Law3997, noS7R12_Law4006⟩
