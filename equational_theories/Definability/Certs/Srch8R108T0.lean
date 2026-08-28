import equational_theories.Definability.Srch_S8R108

/-!
# Structural certificate targets: `Magma.srch8R108` (part 1 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R108_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,558 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R108_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 374 takes them (471 nodes). -/
def ordS8R108_Law374 : List (Fin 18) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- No member of the class satisfies equation 374. -/
theorem noS8R108_Law374 : ∀ v : Magma.tup8R108,
    ¬ @Equation374 (Fin 8) (Magma.srch8R108 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law374) (E := S8R108.E) (tr := S8R108.tr) (z := S8R108.z)
    (st := S8R108.st) (X := S8R108.X) (envs := Magma.envsRed 8 S8R108.E 2)
    (ord := ordS8R108_Law374) (by native_decide) v.1 v.2
    ((@Law374.models_iff (Fin 8) (Magma.srch8R108 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3559 takes them (2087 nodes). -/
def ordS8R108_Law3559 : List (Fin 18) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- No member of the class satisfies equation 3559. -/
theorem noS8R108_Law3559 : ∀ v : Magma.tup8R108,
    ¬ @Equation3559 (Fin 8) (Magma.srch8R108 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3559) (E := S8R108.E) (tr := S8R108.tr) (z := S8R108.z)
    (st := S8R108.st) (X := S8R108.X) (envs := Magma.envsRed 8 S8R108.E 2)
    (ord := ordS8R108_Law3559) (by native_decide) v.1 v.2
    ((@Law3559.models_iff (Fin 8) (Magma.srch8R108 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R108_refutes_0 :
    FamilyRefutes Magma.srch8R108 [
      374, 3559
    ] :=
  ⟨noS8R108_Law374, noS8R108_Law3559⟩
