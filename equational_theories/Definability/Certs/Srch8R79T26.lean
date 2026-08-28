import equational_theories.Definability.Srch_S8R79

/-!
# Structural certificate targets: `Magma.srch8R79` (part 27 of 33)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R79_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 2,190 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R79_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3083 takes them (1054 nodes). -/
def ordS8R79_Law3083 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3083. -/
theorem noS8R79_Law3083 : ∀ v : Magma.tup8R79,
    ¬ @Equation3083 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 3)
    (ord := ordS8R79_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (1054 nodes). -/
def ordS8R79_Law3094 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3094. -/
theorem noS8R79_Law3094 : ∀ v : Magma.tup8R79,
    ¬ @Equation3094 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 3)
    (ord := ordS8R79_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3180 takes them (82 nodes). -/
def ordS8R79_Law3180 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3180. -/
theorem noS8R79_Law3180 : ∀ v : Magma.tup8R79,
    ¬ @Equation3180 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3180) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 3)
    (ord := ordS8R79_Law3180) (by native_decide) v.1 v.2
    ((@Law3180.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch8R79_refutes_26 :
    FamilyRefutes Magma.srch8R79 [
      3083, 3094, 3180
    ] :=
  ⟨noS8R79_Law3083, noS8R79_Law3094, noS8R79_Law3180⟩
