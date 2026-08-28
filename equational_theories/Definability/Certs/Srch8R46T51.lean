import equational_theories.Definability.Srch_S8R46

/-!
# Structural certificate targets: `Magma.srch8R46` (part 52 of 57)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R46_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,152 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R46_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4402 takes them (198 nodes). -/
def ordS8R46_Law4402 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4402. -/
theorem noS8R46_Law4402 : ∀ v : Magma.tup8R46,
    ¬ @Equation4402 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4402) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 3)
    (ord := ordS8R46_Law4402) (by native_decide) v.1 v.2
    ((@Law4402.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4469 takes them (1954 nodes). -/
def ordS8R46_Law4469 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 4469. -/
theorem noS8R46_Law4469 : ∀ v : Magma.tup8R46,
    ¬ @Equation4469 (Fin 8) (Magma.srch8R46 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4469) (E := S8R46.E) (tr := S8R46.tr) (z := S8R46.z)
    (st := S8R46.st) (X := S8R46.X) (envs := Magma.envsRed 8 S8R46.E 2)
    (ord := ordS8R46_Law4469) (by native_decide) v.1 v.2
    ((@Law4469.models_iff (Fin 8) (Magma.srch8R46 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R46_refutes_51 :
    FamilyRefutes Magma.srch8R46 [
      4402, 4469
    ] :=
  ⟨noS8R46_Law4402, noS8R46_Law4469⟩
