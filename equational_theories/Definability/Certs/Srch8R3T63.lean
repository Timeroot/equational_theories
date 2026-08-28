import equational_theories.Definability.Srch_S8R3

/-!
# Structural certificate targets: `Magma.srch8R3` (part 64 of 77)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R3_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 2,889 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R3_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4513 takes them (773 nodes). -/
def ordS8R3_Law4513 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4513. -/
theorem noS8R3_Law4513 : ∀ v : Magma.tup8R3,
    ¬ @Equation4513 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4513) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 4)
    (ord := ordS8R3_Law4513) (by native_decide) v.1 v.2
    ((@Law4513.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4515 takes them (1761 nodes). -/
def ordS8R3_Law4515 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4515. -/
theorem noS8R3_Law4515 : ∀ v : Magma.tup8R3,
    ¬ @Equation4515 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4515) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 3)
    (ord := ordS8R3_Law4515) (by native_decide) v.1 v.2
    ((@Law4515.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4519 takes them (355 nodes). -/
def ordS8R3_Law4519 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4519. -/
theorem noS8R3_Law4519 : ∀ v : Magma.tup8R3,
    ¬ @Equation4519 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4519) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 4)
    (ord := ordS8R3_Law4519) (by native_decide) v.1 v.2
    ((@Law4519.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch8R3_refutes_63 :
    FamilyRefutes Magma.srch8R3 [
      4513, 4515, 4519
    ] :=
  ⟨noS8R3_Law4513, noS8R3_Law4515, noS8R3_Law4519⟩
