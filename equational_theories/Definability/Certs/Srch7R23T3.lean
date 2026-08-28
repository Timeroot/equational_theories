import equational_theories.Definability.Srch_S7R23

/-!
# Structural certificate targets: `Magma.srch7R23` (part 4 of 6)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R23_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,421 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R23_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2536 takes them (696 nodes). -/
def ordS7R23_Law2536 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2536. -/
theorem noS7R23_Law2536 : ∀ v : Magma.tup7R23,
    ¬ @Equation2536 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2536) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law2536) (by native_decide) v.1 v.2
    ((@Law2536.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3587 takes them (128 nodes). -/
def ordS7R23_Law3587 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3587. -/
theorem noS7R23_Law3587 : ∀ v : Magma.tup7R23,
    ¬ @Equation3587 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3587) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law3587) (by native_decide) v.1 v.2
    ((@Law3587.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3601 takes them (863 nodes). -/
def ordS7R23_Law3601 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3601. -/
theorem noS7R23_Law3601 : ∀ v : Magma.tup7R23,
    ¬ @Equation3601 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3601) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law3601) (by native_decide) v.1 v.2
    ((@Law3601.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3919 takes them (554 nodes). -/
def ordS7R23_Law3919 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3919. -/
theorem noS7R23_Law3919 : ∀ v : Magma.tup7R23,
    ¬ @Equation3919 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3919) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law3919) (by native_decide) v.1 v.2
    ((@Law3919.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4007 takes them (1075 nodes). -/
def ordS7R23_Law4007 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4007. -/
theorem noS7R23_Law4007 : ∀ v : Magma.tup7R23,
    ¬ @Equation4007 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4007) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4007) (by native_decide) v.1 v.2
    ((@Law4007.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4400 takes them (105 nodes). -/
def ordS7R23_Law4400 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4400. -/
theorem noS7R23_Law4400 : ∀ v : Magma.tup7R23,
    ¬ @Equation4400 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4400) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4400) (by native_decide) v.1 v.2
    ((@Law4400.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch7R23_refutes_3 :
    FamilyRefutes Magma.srch7R23 [
      2536, 3587, 3601, 3919, 4007, 4400
    ] :=
  ⟨noS7R23_Law2536, noS7R23_Law3587, noS7R23_Law3601, noS7R23_Law3919, noS7R23_Law4007, noS7R23_Law4400⟩
