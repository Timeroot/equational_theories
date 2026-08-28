import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 32 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 3,554 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3066 takes them (804 nodes). -/
def ordS7R12_Law3066 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3066. -/
theorem noS7R12_Law3066 : ∀ v : Magma.tup7R12,
    ¬ @Equation3066 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3071 takes them (342 nodes). -/
def ordS7R12_Law3071 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3071. -/
theorem noS7R12_Law3071 : ∀ v : Magma.tup7R12,
    ¬ @Equation3071 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3071) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3071) (by native_decide) v.1 v.2
    ((@Law3071.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3078 takes them (395 nodes). -/
def ordS7R12_Law3078 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3078. -/
theorem noS7R12_Law3078 : ∀ v : Magma.tup7R12,
    ¬ @Equation3078 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3078) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3078) (by native_decide) v.1 v.2
    ((@Law3078.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3079 takes them (936 nodes). -/
def ordS7R12_Law3079 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3079. -/
theorem noS7R12_Law3079 : ∀ v : Magma.tup7R12,
    ¬ @Equation3079 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3079) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3079) (by native_decide) v.1 v.2
    ((@Law3079.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3081 takes them (198 nodes). -/
def ordS7R12_Law3081 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3081. -/
theorem noS7R12_Law3081 : ∀ v : Magma.tup7R12,
    ¬ @Equation3081 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3081) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3081) (by native_decide) v.1 v.2
    ((@Law3081.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (428 nodes). -/
def ordS7R12_Law3083 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3083. -/
theorem noS7R12_Law3083 : ∀ v : Magma.tup7R12,
    ¬ @Equation3083 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3089 takes them (191 nodes). -/
def ordS7R12_Law3089 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3089. -/
theorem noS7R12_Law3089 : ∀ v : Magma.tup7R12,
    ¬ @Equation3089 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3089) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3089) (by native_decide) v.1 v.2
    ((@Law3089.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (260 nodes). -/
def ordS7R12_Law3091 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3091. -/
theorem noS7R12_Law3091 : ∀ v : Magma.tup7R12,
    ¬ @Equation3091 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch7R12_refutes_31 :
    FamilyRefutes Magma.srch7R12 [
      3066, 3071, 3078, 3079, 3081, 3083, 3089, 3091
    ] :=
  ⟨noS7R12_Law3066, noS7R12_Law3071, noS7R12_Law3078, noS7R12_Law3079, noS7R12_Law3081, noS7R12_Law3083, noS7R12_Law3089, noS7R12_Law3091⟩
