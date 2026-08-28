import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 21 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,381 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4606 takes them (1097 nodes). -/
def ordS8R52_Law4606 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4606. -/
theorem noS8R52_Law4606 : ∀ v : Magma.tup8R52,
    ¬ @Equation4606 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4606) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4606) (by native_decide) v.1 v.2
    ((@Law4606.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4615 takes them (417 nodes). -/
def ordS8R52_Law4615 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4615. -/
theorem noS8R52_Law4615 : ∀ v : Magma.tup8R52,
    ¬ @Equation4615 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4615) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law4615) (by native_decide) v.1 v.2
    ((@Law4615.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4629 takes them (295 nodes). -/
def ordS8R52_Law4629 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4629. -/
theorem noS8R52_Law4629 : ∀ v : Magma.tup8R52,
    ¬ @Equation4629 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4629) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4629) (by native_decide) v.1 v.2
    ((@Law4629.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (225 nodes). -/
def ordS8R52_Law4635 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4635. -/
theorem noS8R52_Law4635 : ∀ v : Magma.tup8R52,
    ¬ @Equation4635 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4645 takes them (465 nodes). -/
def ordS8R52_Law4645 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4645. -/
theorem noS8R52_Law4645 : ∀ v : Magma.tup8R52,
    ¬ @Equation4645 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4645) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law4645) (by native_decide) v.1 v.2
    ((@Law4645.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4656 takes them (481 nodes). -/
def ordS8R52_Law4656 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4656. -/
theorem noS8R52_Law4656 : ∀ v : Magma.tup8R52,
    ¬ @Equation4656 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4656) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law4656) (by native_decide) v.1 v.2
    ((@Law4656.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4689 takes them (401 nodes). -/
def ordS8R52_Law4689 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4689. -/
theorem noS8R52_Law4689 : ∀ v : Magma.tup8R52,
    ¬ @Equation4689 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4689) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law4689) (by native_decide) v.1 v.2
    ((@Law4689.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch8R52_refutes_20 :
    FamilyRefutes Magma.srch8R52 [
      4606, 4615, 4629, 4635, 4645, 4656, 4689
    ] :=
  ⟨noS8R52_Law4606, noS8R52_Law4615, noS8R52_Law4629, noS8R52_Law4635, noS8R52_Law4645, noS8R52_Law4656, noS8R52_Law4689⟩
