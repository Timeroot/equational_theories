import equational_theories.Definability.Srch_S8R46

/-!
# Structural certificate targets: `Magma.srch8R46` (part 51 of 57)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R46_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,882 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R46_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4388 takes them (1954 nodes). -/
def ordS8R46_Law4388 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4388. -/
theorem noS8R46_Law4388 : ∀ v : Magma.tup8R46,
    ¬ @Equation4388 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4388) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 2)
    (ord := ordS8R46_Law4388) (by native_decide) v.1 v.2
    ((@Law4388.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4391 takes them (1928 nodes). -/
def ordS8R46_Law4391 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4391. -/
theorem noS8R46_Law4391 : ∀ v : Magma.tup8R46,
    ¬ @Equation4391 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4391) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law4391) (by native_decide) v.1 v.2
    ((@Law4391.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R46_refutes_50 :
    FamilyRefutes Magma.srch8R46 [
      4388, 4391
    ] :=
  ⟨noS8R46_Law4388, noS8R46_Law4391⟩
