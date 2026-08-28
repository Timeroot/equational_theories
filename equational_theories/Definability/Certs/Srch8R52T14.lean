import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 15 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 3,612 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3343 takes them (279 nodes). -/
def ordS8R52_Law3343 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3343. -/
theorem noS8R52_Law3343 : ∀ v : Magma.tup8R52,
    ¬ @Equation3343 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3484 takes them (221 nodes). -/
def ordS8R52_Law3484 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3484. -/
theorem noS8R52_Law3484 : ∀ v : Magma.tup8R52,
    ¬ @Equation3484 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3484) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3484) (by native_decide) v.1 v.2
    ((@Law3484.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (159 nodes). -/
def ordS8R52_Law3511 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3511. -/
theorem noS8R52_Law3511 : ∀ v : Magma.tup8R52,
    ¬ @Equation3511 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3520 takes them (405 nodes). -/
def ordS8R52_Law3520 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3520. -/
theorem noS8R52_Law3520 : ∀ v : Magma.tup8R52,
    ¬ @Equation3520 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3520) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3520) (by native_decide) v.1 v.2
    ((@Law3520.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3521 takes them (1097 nodes). -/
def ordS8R52_Law3521 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3521. -/
theorem noS8R52_Law3521 : ∀ v : Magma.tup8R52,
    ¬ @Equation3521 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3521) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3521) (by native_decide) v.1 v.2
    ((@Law3521.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3523 takes them (405 nodes). -/
def ordS8R52_Law3523 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3523. -/
theorem noS8R52_Law3523 : ∀ v : Magma.tup8R52,
    ¬ @Equation3523 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3523) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3523) (by native_decide) v.1 v.2
    ((@Law3523.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3524 takes them (453 nodes). -/
def ordS8R52_Law3524 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3524. -/
theorem noS8R52_Law3524 : ∀ v : Magma.tup8R52,
    ¬ @Equation3524 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3524) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3524) (by native_decide) v.1 v.2
    ((@Law3524.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3527 takes them (405 nodes). -/
def ordS8R52_Law3527 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3527. -/
theorem noS8R52_Law3527 : ∀ v : Magma.tup8R52,
    ¬ @Equation3527 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3527) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law3527) (by native_decide) v.1 v.2
    ((@Law3527.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3533 takes them (188 nodes). -/
def ordS8R52_Law3533 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3533. -/
theorem noS8R52_Law3533 : ∀ v : Magma.tup8R52,
    ¬ @Equation3533 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3533) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3533) (by native_decide) v.1 v.2
    ((@Law3533.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch8R52_refutes_14 :
    FamilyRefutes Magma.srch8R52 [
      3343, 3484, 3511, 3520, 3521, 3523, 3524, 3527, 3533
    ] :=
  ⟨noS8R52_Law3343, noS8R52_Law3484, noS8R52_Law3511, noS8R52_Law3520, noS8R52_Law3521, noS8R52_Law3523, noS8R52_Law3524, noS8R52_Law3527, noS8R52_Law3533⟩
