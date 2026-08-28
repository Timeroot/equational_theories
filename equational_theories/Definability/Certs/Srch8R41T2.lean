import equational_theories.Definability.Srch_S8R41

/-!
# Structural certificate targets: `Magma.srch8R41` (part 3 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R41_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,634 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R41_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3566 takes them (330 nodes). -/
def ordS8R41_Law3566 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3566. -/
theorem noS8R41_Law3566 : ∀ v : Magma.tup8R41,
    ¬ @Equation3566 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3566) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3566) (by native_decide) v.1 v.2
    ((@Law3566.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3716 takes them (274 nodes). -/
def ordS8R41_Law3716 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3716. -/
theorem noS8R41_Law3716 : ∀ v : Magma.tup8R41,
    ¬ @Equation3716 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3716) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3716) (by native_decide) v.1 v.2
    ((@Law3716.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3790 takes them (367 nodes). -/
def ordS8R41_Law3790 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3790. -/
theorem noS8R41_Law3790 : ∀ v : Magma.tup8R41,
    ¬ @Equation3790 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3790) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3790) (by native_decide) v.1 v.2
    ((@Law3790.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3930 takes them (310 nodes). -/
def ordS8R41_Law3930 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3930. -/
theorem noS8R41_Law3930 : ∀ v : Magma.tup8R41,
    ¬ @Equation3930 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3930) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3930) (by native_decide) v.1 v.2
    ((@Law3930.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3972 takes them (759 nodes). -/
def ordS8R41_Law3972 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3972. -/
theorem noS8R41_Law3972 : ∀ v : Magma.tup8R41,
    ¬ @Equation3972 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3972) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3972) (by native_decide) v.1 v.2
    ((@Law3972.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3989 takes them (891 nodes). -/
def ordS8R41_Law3989 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3989. -/
theorem noS8R41_Law3989 : ∀ v : Magma.tup8R41,
    ¬ @Equation3989 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3989) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 3)
    (ord := ordS8R41_Law3989) (by native_decide) v.1 v.2
    ((@Law3989.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4040 takes them (703 nodes). -/
def ordS8R41_Law4040 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4040. -/
theorem noS8R41_Law4040 : ∀ v : Magma.tup8R41,
    ¬ @Equation4040 (Fin 8) (Magma.srch8R41 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4040) (E := S8R41.E) (tr := S8R41.tr) (z := S8R41.z)
    (st := S8R41.st) (X := S8R41.X) (envs := Magma.envsRed 8 S8R41.E 4)
    (ord := ordS8R41_Law4040) (by native_decide) v.1 v.2
    ((@Law4040.models_iff (Fin 8) (Magma.srch8R41 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch8R41_refutes_2 :
    FamilyRefutes Magma.srch8R41 [
      3566, 3716, 3790, 3930, 3972, 3989, 4040
    ] :=
  ⟨noS8R41_Law3566, noS8R41_Law3716, noS8R41_Law3790, noS8R41_Law3930, noS8R41_Law3972, noS8R41_Law3989, noS8R41_Law4040⟩
