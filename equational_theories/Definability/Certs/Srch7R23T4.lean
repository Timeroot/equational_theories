import equational_theories.Definability.Srch_S7R23

/-!
# Structural certificate targets: `Magma.srch7R23` (part 5 of 6)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R23_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,661 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R23_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4402 takes them (312 nodes). -/
def ordS7R23_Law4402 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4402. -/
theorem noS7R23_Law4402 : ∀ v : Magma.tup7R23,
    ¬ @Equation4402 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4402) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4402) (by native_decide) v.1 v.2
    ((@Law4402.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4404 takes them (61 nodes). -/
def ordS7R23_Law4404 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4404. -/
theorem noS7R23_Law4404 : ∀ v : Magma.tup7R23,
    ¬ @Equation4404 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4404) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4404) (by native_decide) v.1 v.2
    ((@Law4404.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4416 takes them (913 nodes). -/
def ordS7R23_Law4416 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4416. -/
theorem noS7R23_Law4416 : ∀ v : Magma.tup7R23,
    ¬ @Equation4416 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4416) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4416) (by native_decide) v.1 v.2
    ((@Law4416.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4428 takes them (83 nodes). -/
def ordS7R23_Law4428 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4428. -/
theorem noS7R23_Law4428 : ∀ v : Magma.tup7R23,
    ¬ @Equation4428 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4428) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4428) (by native_decide) v.1 v.2
    ((@Law4428.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4511 takes them (980 nodes). -/
def ordS7R23_Law4511 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4511. -/
theorem noS7R23_Law4511 : ∀ v : Magma.tup7R23,
    ¬ @Equation4511 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4511) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4511) (by native_decide) v.1 v.2
    ((@Law4511.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4512 takes them (1124 nodes). -/
def ordS7R23_Law4512 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4512. -/
theorem noS7R23_Law4512 : ∀ v : Magma.tup7R23,
    ¬ @Equation4512 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4512) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 3)
    (ord := ordS7R23_Law4512) (by native_decide) v.1 v.2
    ((@Law4512.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4513 takes them (188 nodes). -/
def ordS7R23_Law4513 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4513. -/
theorem noS7R23_Law4513 : ∀ v : Magma.tup7R23,
    ¬ @Equation4513 (Fin 7) (Magma.srch7R23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4513) (E := S7R23.E) (tr := S7R23.tr) (z := S7R23.z)
    (st := S7R23.st) (X := S7R23.X) (envs := Magma.envsRed 7 S7R23.E 4)
    (ord := ordS7R23_Law4513) (by native_decide) v.1 v.2
    ((@Law4513.models_iff (Fin 7) (Magma.srch7R23 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch7R23_refutes_4 :
    FamilyRefutes Magma.srch7R23 [
      4402, 4404, 4416, 4428, 4511, 4512, 4513
    ] :=
  ⟨noS7R23_Law4402, noS7R23_Law4404, noS7R23_Law4416, noS7R23_Law4428, noS7R23_Law4511, noS7R23_Law4512, noS7R23_Law4513⟩
