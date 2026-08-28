import equational_theories.Definability.Srch_S8R51

/-!
# Structural certificate targets: `Magma.srch8R51` (part 10 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R51_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,844 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R51_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3868 takes them (760 nodes). -/
def ordS8R51_Law3868 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3868. -/
theorem noS8R51_Law3868 : ∀ v : Magma.tup8R51,
    ¬ @Equation3868 (Fin 8) (Magma.srch8R51 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3868) (E := S8R51.E) (tr := S8R51.tr) (z := S8R51.z)
    (st := S8R51.st) (X := S8R51.X) (envs := Magma.envsRed 8 S8R51.E 2)
    (ord := ordS8R51_Law3868) (by native_decide) v.1 v.2
    ((@Law3868.models_iff (Fin 8) (Magma.srch8R51 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4074 takes them (3084 nodes). -/
def ordS8R51_Law4074 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4074. -/
theorem noS8R51_Law4074 : ∀ v : Magma.tup8R51,
    ¬ @Equation4074 (Fin 8) (Magma.srch8R51 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4074) (E := S8R51.E) (tr := S8R51.tr) (z := S8R51.z)
    (st := S8R51.st) (X := S8R51.X) (envs := Magma.envsRed 8 S8R51.E 2)
    (ord := ordS8R51_Law4074) (by native_decide) v.1 v.2
    ((@Law4074.models_iff (Fin 8) (Magma.srch8R51 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R51_refutes_9 :
    FamilyRefutes Magma.srch8R51 [
      3868, 4074
    ] :=
  ⟨noS8R51_Law3868, noS8R51_Law4074⟩
