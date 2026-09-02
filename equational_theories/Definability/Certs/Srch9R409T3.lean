import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 4 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 2,759 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 266 takes them (672 nodes). -/
def ordS9R409_Law266 : List (Fin 12) := [9, 0, 5, 10, 4, 3, 2, 7, 11, 1, 8, 6]

/-- No member of the class satisfies equation 266. -/
theorem noS9R409_Law266 : ∀ v : Magma.tup9R409,
    ¬ @Equation266 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law266) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law266) (by native_decide) v.1 v.2
    ((@Law266.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 446 takes them (1152 nodes). -/
def ordS9R409_Law446 : List (Fin 12) := [5, 9, 0, 8, 11, 4, 7, 2, 6, 10, 1, 3]

/-- No member of the class satisfies equation 446. -/
theorem noS9R409_Law446 : ∀ v : Magma.tup9R409,
    ¬ @Equation446 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law446) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law446) (by native_decide) v.1 v.2
    ((@Law446.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 450 takes them (935 nodes). -/
def ordS9R409_Law450 : List (Fin 12) := [7, 9, 6, 4, 8, 11, 1, 3, 10, 2, 5, 0]

/-- No member of the class satisfies equation 450. -/
theorem noS9R409_Law450 : ∀ v : Magma.tup9R409,
    ¬ @Equation450 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law450) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law450) (by native_decide) v.1 v.2
    ((@Law450.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch9R409_refutes_3 :
    FamilyRefutes Magma.srch9R409 [
      266, 446, 450
    ] :=
  ⟨noS9R409_Law266, noS9R409_Law446, noS9R409_Law450⟩
