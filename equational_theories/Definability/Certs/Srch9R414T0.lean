import equational_theories.Definability.Srch_S9R414

/-!
# Structural certificate targets: `Magma.srch9R414`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R414_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,676 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R414_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3481 takes them (1042 nodes). -/
def ordS9R414_Law3481 : List (Fin 11) := [10, 5, 8, 9, 6, 4, 1, 3, 0, 2, 7]

/-- No member of the class satisfies equation 3481. -/
theorem noS9R414_Law3481 : ∀ v : Magma.tup9R414,
    ¬ @Equation3481 (Fin 9) (Magma.srch9R414 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3481) (E := S9R414.E) (tr := S9R414.tr) (z := S9R414.z)
    (st := S9R414.st) (X := S9R414.X) (envs := Magma.envsRed 9 S9R414.E 2)
    (ord := ordS9R414_Law3481) (by native_decide) v.1 v.2
    ((@Law3481.models_iff (Fin 9) (Magma.srch9R414 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3865 takes them (1634 nodes). -/
def ordS9R414_Law3865 : List (Fin 11) := [5, 4, 1, 6, 8, 10, 2, 0, 9, 7, 3]

/-- No member of the class satisfies equation 3865. -/
theorem noS9R414_Law3865 : ∀ v : Magma.tup9R414,
    ¬ @Equation3865 (Fin 9) (Magma.srch9R414 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3865) (E := S9R414.E) (tr := S9R414.tr) (z := S9R414.z)
    (st := S9R414.st) (X := S9R414.X) (envs := Magma.envsRed 9 S9R414.E 2)
    (ord := ordS9R414_Law3865) (by native_decide) v.1 v.2
    ((@Law3865.models_iff (Fin 9) (Magma.srch9R414 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch9R414_refutes_0 :
    FamilyRefutes Magma.srch9R414 [
      3481, 3865
    ] :=
  ⟨noS9R414_Law3481, noS9R414_Law3865⟩
