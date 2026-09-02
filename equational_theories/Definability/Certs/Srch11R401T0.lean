import equational_theories.Definability.Srch_S11R401

/-!
# Structural certificate targets: `Magma.srch11R401`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R401_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 292 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R401_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3548 takes them (65 nodes). -/
def ordS11R401_Law3548 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3548. -/
theorem noS11R401_Law3548 : ∀ v : Magma.tup11R401,
    ¬ @Equation3548 (Fin 11) (Magma.srch11R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3548) (E := S11R401.E) (tr := S11R401.tr) (z := S11R401.z)
    (st := S11R401.st) (X := S11R401.X) (envs := Magma.envsRed 11 S11R401.E 2)
    (ord := ordS11R401_Law3548) (by native_decide) v.1 v.2
    ((@Law3548.models_iff (Fin 11) (Magma.srch11R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3675 takes them (31 nodes). -/
def ordS11R401_Law3675 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3675. -/
theorem noS11R401_Law3675 : ∀ v : Magma.tup11R401,
    ¬ @Equation3675 (Fin 11) (Magma.srch11R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3675) (E := S11R401.E) (tr := S11R401.tr) (z := S11R401.z)
    (st := S11R401.st) (X := S11R401.X) (envs := Magma.envsRed 11 S11R401.E 2)
    (ord := ordS11R401_Law3675) (by native_decide) v.1 v.2
    ((@Law3675.models_iff (Fin 11) (Magma.srch11R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3703 takes them (18 nodes). -/
def ordS11R401_Law3703 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3703. -/
theorem noS11R401_Law3703 : ∀ v : Magma.tup11R401,
    ¬ @Equation3703 (Fin 11) (Magma.srch11R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3703) (E := S11R401.E) (tr := S11R401.tr) (z := S11R401.z)
    (st := S11R401.st) (X := S11R401.X) (envs := Magma.envsRed 11 S11R401.E 3)
    (ord := ordS11R401_Law3703) (by native_decide) v.1 v.2
    ((@Law3703.models_iff (Fin 11) (Magma.srch11R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3954 takes them (108 nodes). -/
def ordS11R401_Law3954 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3954. -/
theorem noS11R401_Law3954 : ∀ v : Magma.tup11R401,
    ¬ @Equation3954 (Fin 11) (Magma.srch11R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3954) (E := S11R401.E) (tr := S11R401.tr) (z := S11R401.z)
    (st := S11R401.st) (X := S11R401.X) (envs := Magma.envsRed 11 S11R401.E 2)
    (ord := ordS11R401_Law3954) (by native_decide) v.1 v.2
    ((@Law3954.models_iff (Fin 11) (Magma.srch11R401 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4405 takes them (70 nodes). -/
def ordS11R401_Law4405 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4405. -/
theorem noS11R401_Law4405 : ∀ v : Magma.tup11R401,
    ¬ @Equation4405 (Fin 11) (Magma.srch11R401 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4405) (E := S11R401.E) (tr := S11R401.tr) (z := S11R401.z)
    (st := S11R401.st) (X := S11R401.X) (envs := Magma.envsRed 11 S11R401.E 2)
    (ord := ordS11R401_Law4405) (by native_decide) v.1 v.2
    ((@Law4405.models_iff (Fin 11) (Magma.srch11R401 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch11R401_refutes_0 :
    FamilyRefutes Magma.srch11R401 [
      3548, 3675, 3703, 3954, 4405
    ] :=
  ⟨noS11R401_Law3548, noS11R401_Law3675, noS11R401_Law3703, noS11R401_Law3954, noS11R401_Law4405⟩
