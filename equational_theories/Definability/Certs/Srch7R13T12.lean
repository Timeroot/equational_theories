import equational_theories.Definability.Srch_S7R13

/-!
# Structural certificate targets: `Magma.srch7R13` (part 13 of 17)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,023 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3278 takes them (765 nodes). -/
def ordS7R13_Law3278 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3278. -/
theorem noS7R13_Law3278 : ∀ v : Magma.tup7R13,
    ¬ @Equation3278 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3278) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law3278) (by native_decide) v.1 v.2
    ((@Law3278.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3321 takes them (189 nodes). -/
def ordS7R13_Law3321 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3321. -/
theorem noS7R13_Law3321 : ∀ v : Magma.tup7R13,
    ¬ @Equation3321 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3321) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law3321) (by native_decide) v.1 v.2
    ((@Law3321.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3323 takes them (193 nodes). -/
def ordS7R13_Law3323 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3323. -/
theorem noS7R13_Law3323 : ∀ v : Magma.tup7R13,
    ¬ @Equation3323 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3323) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law3323) (by native_decide) v.1 v.2
    ((@Law3323.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3324 takes them (181 nodes). -/
def ordS7R13_Law3324 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3324. -/
theorem noS7R13_Law3324 : ∀ v : Magma.tup7R13,
    ¬ @Equation3324 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3324) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 4)
    (ord := ordS7R13_Law3324) (by native_decide) v.1 v.2
    ((@Law3324.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (954 nodes). -/
def ordS7R13_Law3334 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3334. -/
theorem noS7R13_Law3334 : ∀ v : Magma.tup7R13,
    ¬ @Equation3334 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (741 nodes). -/
def ordS7R13_Law3414 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3414. -/
theorem noS7R13_Law3414 : ∀ v : Magma.tup7R13,
    ¬ @Equation3414 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch7R13_refutes_12 :
    FamilyRefutes Magma.srch7R13 [
      3278, 3321, 3323, 3324, 3334, 3414
    ] :=
  ⟨noS7R13_Law3278, noS7R13_Law3321, noS7R13_Law3323, noS7R13_Law3324, noS7R13_Law3334, noS7R13_Law3414⟩
