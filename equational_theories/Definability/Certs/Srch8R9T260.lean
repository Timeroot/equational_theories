import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 261 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `5`
equations here, 3,228 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4569 takes them (741 nodes). -/
def ordS8R9_Law4569 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4569. -/
theorem noS8R9_Law4569 : ∀ v : Magma.tup8R9,
    ¬ @Equation4569 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4569) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4569) (by native_decide) v.1 v.2
    ((@Law4569.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4574 takes them (9 nodes). -/
def ordS8R9_Law4574 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4574. -/
theorem noS8R9_Law4574 : ∀ v : Magma.tup8R9,
    ¬ @Equation4574 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4574) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4574) (by native_decide) v.1 v.2
    ((@Law4574.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4579 takes them (10 nodes). -/
def ordS8R9_Law4579 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4579. -/
theorem noS8R9_Law4579 : ∀ v : Magma.tup8R9,
    ¬ @Equation4579 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4579) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law4579) (by native_decide) v.1 v.2
    ((@Law4579.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4597 takes them (65 nodes). -/
def ordS8R9_Law4597 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4597. -/
theorem noS8R9_Law4597 : ∀ v : Magma.tup8R9,
    ¬ @Equation4597 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4597) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4597) (by native_decide) v.1 v.2
    ((@Law4597.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4600 takes them (2403 nodes). -/
def ordS8R9_Law4600 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4600. -/
theorem noS8R9_Law4600 : ∀ v : Magma.tup8R9,
    ¬ @Equation4600 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4600) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4600) (by native_decide) v.1 v.2
    ((@Law4600.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch8R9_refutes_260 :
    FamilyRefutes Magma.srch8R9 [
      4569, 4574, 4579, 4597, 4600
    ] :=
  ⟨noS8R9_Law4569, noS8R9_Law4574, noS8R9_Law4579, noS8R9_Law4597, noS8R9_Law4600⟩
