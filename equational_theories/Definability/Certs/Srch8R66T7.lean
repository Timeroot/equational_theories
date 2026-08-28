import equational_theories.Definability.Srch_S8R66

/-!
# Structural certificate targets: `Magma.srch8R66` (part 8 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R66_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 1,904 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R66_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3334 takes them (441 nodes). -/
def ordS8R66_Law3334 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3334. -/
theorem noS8R66_Law3334 : ∀ v : Magma.tup8R66,
    ¬ @Equation3334 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (458 nodes). -/
def ordS8R66_Law3526 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3526. -/
theorem noS8R66_Law3526 : ∀ v : Magma.tup8R66,
    ¬ @Equation3526 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (460 nodes). -/
def ordS8R66_Law4023 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4023. -/
theorem noS8R66_Law4023 : ∀ v : Magma.tup8R66,
    ¬ @Equation4023 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (545 nodes). -/
def ordS8R66_Law4146 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4146. -/
theorem noS8R66_Law4146 : ∀ v : Magma.tup8R66,
    ¬ @Equation4146 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R66_refutes_7 :
    FamilyRefutes Magma.srch8R66 [
      3334, 3526, 4023, 4146
    ] :=
  ⟨noS8R66_Law3334, noS8R66_Law3526, noS8R66_Law4023, noS8R66_Law4146⟩
