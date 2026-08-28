import equational_theories.Definability.Srch_S8R54

/-!
# Structural certificate targets: `Magma.srch8R54` (part 11 of 14)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R54_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 2,878 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R54_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3955 takes them (165 nodes). -/
def ordS8R54_Law3955 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3955. -/
theorem noS8R54_Law3955 : ∀ v : Magma.tup8R54,
    ¬ @Equation3955 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4068 takes them (801 nodes). -/
def ordS8R54_Law4068 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4068. -/
theorem noS8R54_Law4068 : ∀ v : Magma.tup8R54,
    ¬ @Equation4068 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4068) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law4068) (by native_decide) v.1 v.2
    ((@Law4068.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (201 nodes). -/
def ordS8R54_Law4130 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4130. -/
theorem noS8R54_Law4130 : ∀ v : Magma.tup8R54,
    ¬ @Equation4130 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (737 nodes). -/
def ordS8R54_Law4135 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4135. -/
theorem noS8R54_Law4135 : ∀ v : Magma.tup8R54,
    ¬ @Equation4135 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (809 nodes). -/
def ordS8R54_Law4146 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4146. -/
theorem noS8R54_Law4146 : ∀ v : Magma.tup8R54,
    ¬ @Equation4146 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 3)
    (ord := ordS8R54_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (165 nodes). -/
def ordS8R54_Law4158 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4158. -/
theorem noS8R54_Law4158 : ∀ v : Magma.tup8R54,
    ¬ @Equation4158 (Fin 8) (Magma.srch8R54 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S8R54.E) (tr := S8R54.tr) (z := S8R54.z)
    (st := S8R54.st) (X := S8R54.X) (envs := Magma.envsRed 8 S8R54.E 2)
    (ord := ordS8R54_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 8) (Magma.srch8R54 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R54_refutes_10 :
    FamilyRefutes Magma.srch8R54 [
      3955, 4068, 4130, 4135, 4146, 4158
    ] :=
  ⟨noS8R54_Law3955, noS8R54_Law4068, noS8R54_Law4130, noS8R54_Law4135, noS8R54_Law4146, noS8R54_Law4158⟩
