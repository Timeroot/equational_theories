import equational_theories.Definability.Srch_S8R43

/-!
# Structural certificate targets: `Magma.srch8R43` (part 3 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R43_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,465 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R43_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3529 takes them (977 nodes). -/
def ordS8R43_Law3529 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3529. -/
theorem noS8R43_Law3529 : ∀ v : Magma.tup8R43,
    ¬ @Equation3529 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3529) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3529) (by native_decide) v.1 v.2
    ((@Law3529.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3600 takes them (134 nodes). -/
def ordS8R43_Law3600 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3600. -/
theorem noS8R43_Law3600 : ∀ v : Magma.tup8R43,
    ¬ @Equation3600 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3600) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3600) (by native_decide) v.1 v.2
    ((@Law3600.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3926 takes them (84 nodes). -/
def ordS8R43_Law3926 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3926. -/
theorem noS8R43_Law3926 : ∀ v : Magma.tup8R43,
    ¬ @Equation3926 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3926) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3926) (by native_decide) v.1 v.2
    ((@Law3926.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3931 takes them (1192 nodes). -/
def ordS8R43_Law3931 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3931. -/
theorem noS8R43_Law3931 : ∀ v : Magma.tup8R43,
    ¬ @Equation3931 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3931) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3931) (by native_decide) v.1 v.2
    ((@Law3931.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3972 takes them (604 nodes). -/
def ordS8R43_Law3972 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3972. -/
theorem noS8R43_Law3972 : ∀ v : Magma.tup8R43,
    ¬ @Equation3972 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3972) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3972) (by native_decide) v.1 v.2
    ((@Law3972.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3989 takes them (474 nodes). -/
def ordS8R43_Law3989 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3989. -/
theorem noS8R43_Law3989 : ∀ v : Magma.tup8R43,
    ¬ @Equation3989 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3989) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law3989) (by native_decide) v.1 v.2
    ((@Law3989.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R43_refutes_2 :
    FamilyRefutes Magma.srch8R43 [
      3529, 3600, 3926, 3931, 3972, 3989
    ] :=
  ⟨noS8R43_Law3529, noS8R43_Law3600, noS8R43_Law3926, noS8R43_Law3931, noS8R43_Law3972, noS8R43_Law3989⟩
