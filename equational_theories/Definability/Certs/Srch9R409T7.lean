import equational_theories.Definability.Srch_S9R409

/-!
# Structural certificate targets: `Magma.srch9R409` (part 8 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R409_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 2,886 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R409_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 657 takes them (958 nodes). -/
def ordS9R409_Law657 : List (Fin 12) := [0, 2, 4, 8, 10, 11, 5, 6, 3, 7, 1, 9]

/-- No member of the class satisfies equation 657. -/
theorem noS9R409_Law657 : ∀ v : Magma.tup9R409,
    ¬ @Equation657 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law657) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law657) (by native_decide) v.1 v.2
    ((@Law657.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 661 takes them (749 nodes). -/
def ordS9R409_Law661 : List (Fin 12) := [8, 4, 9, 7, 2, 6, 1, 11, 10, 0, 5, 3]

/-- No member of the class satisfies equation 661. -/
theorem noS9R409_Law661 : ∀ v : Magma.tup9R409,
    ¬ @Equation661 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law661) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 4)
    (ord := ordS9R409_Law661) (by native_decide) v.1 v.2
    ((@Law661.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 856 takes them (1179 nodes). -/
def ordS9R409_Law856 : List (Fin 12) := [3, 4, 0, 8, 5, 6, 2, 11, 10, 1, 9, 7]

/-- No member of the class satisfies equation 856. -/
theorem noS9R409_Law856 : ∀ v : Magma.tup9R409,
    ¬ @Equation856 (Fin 9) (Magma.srch9R409 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law856) (E := S9R409.E) (tr := S9R409.tr) (z := S9R409.z)
    (st := S9R409.st) (X := S9R409.X) (envs := Magma.envsRed 9 S9R409.E 3)
    (ord := ordS9R409_Law856) (by native_decide) v.1 v.2
    ((@Law856.models_iff (Fin 9) (Magma.srch9R409 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch9R409_refutes_7 :
    FamilyRefutes Magma.srch9R409 [
      657, 661, 856
    ] :=
  ⟨noS9R409_Law657, noS9R409_Law661, noS9R409_Law856⟩
