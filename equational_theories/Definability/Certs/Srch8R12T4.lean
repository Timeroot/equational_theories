import equational_theories.Definability.Srch_S8R12

/-!
# Structural certificate targets: `Magma.srch8R12` (part 5 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 2,138 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4362 takes them (651 nodes). -/
def ordS8R12_Law4362 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4362. -/
theorem noS8R12_Law4362 : ∀ v : Magma.tup8R12,
    ¬ @Equation4362 (Fin 8) (Magma.srch8R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4362) (E := S8R12.E) (tr := S8R12.tr) (z := S8R12.z)
    (st := S8R12.st) (X := S8R12.X) (envs := Magma.envsRed 8 S8R12.E 3)
    (ord := ordS8R12_Law4362) (by native_decide) v.1 v.2
    ((@Law4362.models_iff (Fin 8) (Magma.srch8R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4401 takes them (156 nodes). -/
def ordS8R12_Law4401 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4401. -/
theorem noS8R12_Law4401 : ∀ v : Magma.tup8R12,
    ¬ @Equation4401 (Fin 8) (Magma.srch8R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4401) (E := S8R12.E) (tr := S8R12.tr) (z := S8R12.z)
    (st := S8R12.st) (X := S8R12.X) (envs := Magma.envsRed 8 S8R12.E 3)
    (ord := ordS8R12_Law4401) (by native_decide) v.1 v.2
    ((@Law4401.models_iff (Fin 8) (Magma.srch8R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4452 takes them (280 nodes). -/
def ordS8R12_Law4452 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4452. -/
theorem noS8R12_Law4452 : ∀ v : Magma.tup8R12,
    ¬ @Equation4452 (Fin 8) (Magma.srch8R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4452) (E := S8R12.E) (tr := S8R12.tr) (z := S8R12.z)
    (st := S8R12.st) (X := S8R12.X) (envs := Magma.envsRed 8 S8R12.E 3)
    (ord := ordS8R12_Law4452) (by native_decide) v.1 v.2
    ((@Law4452.models_iff (Fin 8) (Magma.srch8R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4673 takes them (1051 nodes). -/
def ordS8R12_Law4673 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4673. -/
theorem noS8R12_Law4673 : ∀ v : Magma.tup8R12,
    ¬ @Equation4673 (Fin 8) (Magma.srch8R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4673) (E := S8R12.E) (tr := S8R12.tr) (z := S8R12.z)
    (st := S8R12.st) (X := S8R12.X) (envs := Magma.envsRed 8 S8R12.E 3)
    (ord := ordS8R12_Law4673) (by native_decide) v.1 v.2
    ((@Law4673.models_iff (Fin 8) (Magma.srch8R12 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R12_refutes_4 :
    FamilyRefutes Magma.srch8R12 [
      4362, 4401, 4452, 4673
    ] :=
  ⟨noS8R12_Law4362, noS8R12_Law4401, noS8R12_Law4452, noS8R12_Law4673⟩
