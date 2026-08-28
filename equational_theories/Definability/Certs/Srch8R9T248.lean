import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 249 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `9`
equations here, 3,377 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4348 takes them (2403 nodes). -/
def ordS8R9_Law4348 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4348. -/
theorem noS8R9_Law4348 : ∀ v : Magma.tup8R9,
    ¬ @Equation4348 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4348) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4348) (by native_decide) v.1 v.2
    ((@Law4348.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4351 takes them (65 nodes). -/
def ordS8R9_Law4351 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4351. -/
theorem noS8R9_Law4351 : ∀ v : Magma.tup8R9,
    ¬ @Equation4351 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4351) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4351) (by native_decide) v.1 v.2
    ((@Law4351.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4354 takes them (65 nodes). -/
def ordS8R9_Law4354 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4354. -/
theorem noS8R9_Law4354 : ∀ v : Magma.tup8R9,
    ¬ @Equation4354 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4354) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4354) (by native_decide) v.1 v.2
    ((@Law4354.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4358 takes them (125 nodes). -/
def ordS8R9_Law4358 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4358. -/
theorem noS8R9_Law4358 : ∀ v : Magma.tup8R9,
    ¬ @Equation4358 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4359 takes them (117 nodes). -/
def ordS8R9_Law4359 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4359. -/
theorem noS8R9_Law4359 : ∀ v : Magma.tup8R9,
    ¬ @Equation4359 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4359) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4359) (by native_decide) v.1 v.2
    ((@Law4359.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4361 takes them (65 nodes). -/
def ordS8R9_Law4361 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4361. -/
theorem noS8R9_Law4361 : ∀ v : Magma.tup8R9,
    ¬ @Equation4361 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4361) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law4361) (by native_decide) v.1 v.2
    ((@Law4361.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4367 takes them (407 nodes). -/
def ordS8R9_Law4367 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4367. -/
theorem noS8R9_Law4367 : ∀ v : Magma.tup8R9,
    ¬ @Equation4367 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4367) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4367) (by native_decide) v.1 v.2
    ((@Law4367.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4374 takes them (65 nodes). -/
def ordS8R9_Law4374 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4374. -/
theorem noS8R9_Law4374 : ∀ v : Magma.tup8R9,
    ¬ @Equation4374 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4374) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4374) (by native_decide) v.1 v.2
    ((@Law4374.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4378 takes them (65 nodes). -/
def ordS8R9_Law4378 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4378. -/
theorem noS8R9_Law4378 : ∀ v : Magma.tup8R9,
    ¬ @Equation4378 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4378) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law4378) (by native_decide) v.1 v.2
    ((@Law4378.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch8R9_refutes_248 :
    FamilyRefutes Magma.srch8R9 [
      4348, 4351, 4354, 4358, 4359, 4361, 4367, 4374, 4378
    ] :=
  ⟨noS8R9_Law4348, noS8R9_Law4351, noS8R9_Law4354, noS8R9_Law4358, noS8R9_Law4359, noS8R9_Law4361, noS8R9_Law4367, noS8R9_Law4374, noS8R9_Law4378⟩
