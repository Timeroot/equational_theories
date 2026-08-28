import equational_theories.Definability.Srch_S8R85

/-!
# Structural certificate targets: `Magma.srch8R85` (part 118 of 130)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R85_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,723 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R85_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4409 takes them (2145 nodes). -/
def ordS8R85_Law4409 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4409. -/
theorem noS8R85_Law4409 : ∀ v : Magma.tup8R85,
    ¬ @Equation4409 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4409) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 2)
    (ord := ordS8R85_Law4409) (by native_decide) v.1 v.2
    ((@Law4409.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4424 takes them (578 nodes). -/
def ordS8R85_Law4424 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4424. -/
theorem noS8R85_Law4424 : ∀ v : Magma.tup8R85,
    ¬ @Equation4424 (Fin 8) (Magma.srch8R85 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4424) (E := S8R85.E) (tr := S8R85.tr) (z := S8R85.z)
    (st := S8R85.st) (X := S8R85.X) (envs := Magma.envsRed 8 S8R85.E 3)
    (ord := ordS8R85_Law4424) (by native_decide) v.1 v.2
    ((@Law4424.models_iff (Fin 8) (Magma.srch8R85 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R85_refutes_117 :
    FamilyRefutes Magma.srch8R85 [
      4409, 4424
    ] :=
  ⟨noS8R85_Law4409, noS8R85_Law4424⟩
