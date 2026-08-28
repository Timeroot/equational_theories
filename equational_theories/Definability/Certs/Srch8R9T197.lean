import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 198 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `9`
equations here, 3,334 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3409 takes them (764 nodes). -/
def ordS8R9_Law3409 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3409. -/
theorem noS8R9_Law3409 : ∀ v : Magma.tup8R9,
    ¬ @Equation3409 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3409) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3409) (by native_decide) v.1 v.2
    ((@Law3409.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3418 takes them (768 nodes). -/
def ordS8R9_Law3418 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3418. -/
theorem noS8R9_Law3418 : ∀ v : Magma.tup8R9,
    ¬ @Equation3418 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3418) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3418) (by native_decide) v.1 v.2
    ((@Law3418.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3426 takes them (768 nodes). -/
def ordS8R9_Law3426 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3426. -/
theorem noS8R9_Law3426 : ∀ v : Magma.tup8R9,
    ¬ @Equation3426 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3426) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3426) (by native_decide) v.1 v.2
    ((@Law3426.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3431 takes them (49 nodes). -/
def ordS8R9_Law3431 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3431. -/
theorem noS8R9_Law3431 : ∀ v : Magma.tup8R9,
    ¬ @Equation3431 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3431) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3431) (by native_decide) v.1 v.2
    ((@Law3431.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3436 takes them (49 nodes). -/
def ordS8R9_Law3436 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3436. -/
theorem noS8R9_Law3436 : ∀ v : Magma.tup8R9,
    ¬ @Equation3436 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3436) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3436) (by native_decide) v.1 v.2
    ((@Law3436.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3441 takes them (53 nodes). -/
def ordS8R9_Law3441 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3441. -/
theorem noS8R9_Law3441 : ∀ v : Magma.tup8R9,
    ¬ @Equation3441 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3441) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3441) (by native_decide) v.1 v.2
    ((@Law3441.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3446 takes them (768 nodes). -/
def ordS8R9_Law3446 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3446. -/
theorem noS8R9_Law3446 : ∀ v : Magma.tup8R9,
    ¬ @Equation3446 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3446) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3446) (by native_decide) v.1 v.2
    ((@Law3446.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3451 takes them (50 nodes). -/
def ordS8R9_Law3451 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3451. -/
theorem noS8R9_Law3451 : ∀ v : Magma.tup8R9,
    ¬ @Equation3451 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3451) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law3451) (by native_decide) v.1 v.2
    ((@Law3451.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3466 takes them (65 nodes). -/
def ordS8R9_Law3466 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3466. -/
theorem noS8R9_Law3466 : ∀ v : Magma.tup8R9,
    ¬ @Equation3466 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3466) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3466) (by native_decide) v.1 v.2
    ((@Law3466.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch8R9_refutes_197 :
    FamilyRefutes Magma.srch8R9 [
      3409, 3418, 3426, 3431, 3436, 3441, 3446, 3451, 3466
    ] :=
  ⟨noS8R9_Law3409, noS8R9_Law3418, noS8R9_Law3426, noS8R9_Law3431, noS8R9_Law3436, noS8R9_Law3441, noS8R9_Law3446, noS8R9_Law3451, noS8R9_Law3466⟩
