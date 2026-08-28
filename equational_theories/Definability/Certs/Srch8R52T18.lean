import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 19 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,154 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4314 takes them (1097 nodes). -/
def ordS8R52_Law4314 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4314. -/
theorem noS8R52_Law4314 : ∀ v : Magma.tup8R52,
    ¬ @Equation4314 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4314) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4314) (by native_decide) v.1 v.2
    ((@Law4314.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4315 takes them (453 nodes). -/
def ordS8R52_Law4315 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4315. -/
theorem noS8R52_Law4315 : ∀ v : Magma.tup8R52,
    ¬ @Equation4315 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4315) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law4315) (by native_decide) v.1 v.2
    ((@Law4315.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4339 takes them (405 nodes). -/
def ordS8R52_Law4339 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4339. -/
theorem noS8R52_Law4339 : ∀ v : Magma.tup8R52,
    ¬ @Equation4339 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4339) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law4339) (by native_decide) v.1 v.2
    ((@Law4339.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4357 takes them (397 nodes). -/
def ordS8R52_Law4357 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4357. -/
theorem noS8R52_Law4357 : ∀ v : Magma.tup8R52,
    ¬ @Equation4357 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4357) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law4357) (by native_decide) v.1 v.2
    ((@Law4357.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4385 takes them (406 nodes). -/
def ordS8R52_Law4385 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4385. -/
theorem noS8R52_Law4385 : ∀ v : Magma.tup8R52,
    ¬ @Equation4385 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4385) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4385) (by native_decide) v.1 v.2
    ((@Law4385.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4395 takes them (396 nodes). -/
def ordS8R52_Law4395 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4395. -/
theorem noS8R52_Law4395 : ∀ v : Magma.tup8R52,
    ¬ @Equation4395 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4395) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4395) (by native_decide) v.1 v.2
    ((@Law4395.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R52_refutes_18 :
    FamilyRefutes Magma.srch8R52 [
      4314, 4315, 4339, 4357, 4385, 4395
    ] :=
  ⟨noS8R52_Law4314, noS8R52_Law4315, noS8R52_Law4339, noS8R52_Law4357, noS8R52_Law4385, noS8R52_Law4395⟩
