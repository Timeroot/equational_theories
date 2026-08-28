import equational_theories.Definability.Srch_S8R13

/-!
# Structural certificate targets: `Magma.srch8R13` (part 35 of 85)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,101 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3552 takes them (1110 nodes). -/
def ordS8R13_Law3552 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3552. -/
theorem noS8R13_Law3552 : ∀ v : Magma.tup8R13,
    ¬ @Equation3552 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3552) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law3552) (by native_decide) v.1 v.2
    ((@Law3552.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3562 takes them (991 nodes). -/
def ordS8R13_Law3562 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3562. -/
theorem noS8R13_Law3562 : ∀ v : Magma.tup8R13,
    ¬ @Equation3562 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3562) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law3562) (by native_decide) v.1 v.2
    ((@Law3562.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R13_refutes_34 :
    FamilyRefutes Magma.srch8R13 [
      3552, 3562
    ] :=
  ⟨noS8R13_Law3552, noS8R13_Law3562⟩
