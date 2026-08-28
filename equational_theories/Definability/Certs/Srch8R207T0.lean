import equational_theories.Definability.Srch_S8R207

/-!
# Structural certificate targets: `Magma.srch8R207`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R207_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 24 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R207_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3353 takes them (4 nodes). -/
def ordS8R207_Law3353 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3353. -/
theorem noS8R207_Law3353 : ∀ v : Magma.tup8R207,
    ¬ @Equation3353 (Fin 8) (Magma.srch8R207 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3353) (E := S8R207.E) (tr := S8R207.tr) (z := S8R207.z)
    (st := S8R207.st) (X := S8R207.X) (envs := Magma.envsRed 8 S8R207.E 2)
    (ord := ordS8R207_Law3353) (by native_decide) v.1 v.2
    ((@Law3353.models_iff (Fin 8) (Magma.srch8R207 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (4 nodes). -/
def ordS8R207_Law3511 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3511. -/
theorem noS8R207_Law3511 : ∀ v : Magma.tup8R207,
    ¬ @Equation3511 (Fin 8) (Magma.srch8R207 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S8R207.E) (tr := S8R207.tr) (z := S8R207.z)
    (st := S8R207.st) (X := S8R207.X) (envs := Magma.envsRed 8 S8R207.E 2)
    (ord := ordS8R207_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 8) (Magma.srch8R207 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (4 nodes). -/
def ordS8R207_Law3955 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 3955. -/
theorem noS8R207_Law3955 : ∀ v : Magma.tup8R207,
    ¬ @Equation3955 (Fin 8) (Magma.srch8R207 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S8R207.E) (tr := S8R207.tr) (z := S8R207.z)
    (st := S8R207.st) (X := S8R207.X) (envs := Magma.envsRed 8 S8R207.E 2)
    (ord := ordS8R207_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 8) (Magma.srch8R207 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4127 takes them (4 nodes). -/
def ordS8R207_Law4127 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4127. -/
theorem noS8R207_Law4127 : ∀ v : Magma.tup8R207,
    ¬ @Equation4127 (Fin 8) (Magma.srch8R207 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4127) (E := S8R207.E) (tr := S8R207.tr) (z := S8R207.z)
    (st := S8R207.st) (X := S8R207.X) (envs := Magma.envsRed 8 S8R207.E 2)
    (ord := ordS8R207_Law4127) (by native_decide) v.1 v.2
    ((@Law4127.models_iff (Fin 8) (Magma.srch8R207 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (4 nodes). -/
def ordS8R207_Law4283 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4283. -/
theorem noS8R207_Law4283 : ∀ v : Magma.tup8R207,
    ¬ @Equation4283 (Fin 8) (Magma.srch8R207 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S8R207.E) (tr := S8R207.tr) (z := S8R207.z)
    (st := S8R207.st) (X := S8R207.X) (envs := Magma.envsRed 8 S8R207.E 2)
    (ord := ordS8R207_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 8) (Magma.srch8R207 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (4 nodes). -/
def ordS8R207_Law4635 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4635. -/
theorem noS8R207_Law4635 : ∀ v : Magma.tup8R207,
    ¬ @Equation4635 (Fin 8) (Magma.srch8R207 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S8R207.E) (tr := S8R207.tr) (z := S8R207.z)
    (st := S8R207.st) (X := S8R207.X) (envs := Magma.envsRed 8 S8R207.E 2)
    (ord := ordS8R207_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 8) (Magma.srch8R207 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R207_refutes_0 :
    FamilyRefutes Magma.srch8R207 [
      3353, 3511, 3955, 4127, 4283, 4635
    ] :=
  ⟨noS8R207_Law3353, noS8R207_Law3511, noS8R207_Law3955, noS8R207_Law4127, noS8R207_Law4283, noS8R207_Law4635⟩
