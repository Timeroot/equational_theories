import equational_theories.Definability.Srch_S10R806

/-!
# Structural certificate targets: `Magma.srch10R806` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R806_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,385 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R806_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2503 takes them (344 nodes). -/
def ordS10R806_Law2503 : List (Fin 10) := [5, 4, 8, 6, 0, 2, 3, 9, 7, 1]

/-- No member of the class satisfies equation 2503. -/
theorem noS10R806_Law2503 : ∀ v : Magma.tup10R806,
    ¬ @Equation2503 (Fin 10) (Magma.srch10R806 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2503) (E := S10R806.E) (tr := S10R806.tr) (z := S10R806.z)
    (st := S10R806.st) (X := S10R806.X) (envs := Magma.envsRed 10 S10R806.E 2)
    (ord := ordS10R806_Law2503) (by native_decide) v.1 v.2
    ((@Law2503.models_iff (Fin 10) (Magma.srch10R806 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2530 takes them (1369 nodes). -/
def ordS10R806_Law2530 : List (Fin 10) := [5, 6, 2, 0, 4, 9, 3, 7, 8, 1]

/-- No member of the class satisfies equation 2530. -/
theorem noS10R806_Law2530 : ∀ v : Magma.tup10R806,
    ¬ @Equation2530 (Fin 10) (Magma.srch10R806 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2530) (E := S10R806.E) (tr := S10R806.tr) (z := S10R806.z)
    (st := S10R806.st) (X := S10R806.X) (envs := Magma.envsRed 10 S10R806.E 2)
    (ord := ordS10R806_Law2530) (by native_decide) v.1 v.2
    ((@Law2530.models_iff (Fin 10) (Magma.srch10R806 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3068 takes them (1672 nodes). -/
def ordS10R806_Law3068 : List (Fin 10) := [1, 9, 7, 6, 0, 8, 5, 4, 2, 3]

/-- No member of the class satisfies equation 3068. -/
theorem noS10R806_Law3068 : ∀ v : Magma.tup10R806,
    ¬ @Equation3068 (Fin 10) (Magma.srch10R806 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3068) (E := S10R806.E) (tr := S10R806.tr) (z := S10R806.z)
    (st := S10R806.st) (X := S10R806.X) (envs := Magma.envsRed 10 S10R806.E 2)
    (ord := ordS10R806_Law3068) (by native_decide) v.1 v.2
    ((@Law3068.models_iff (Fin 10) (Magma.srch10R806 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R806_refutes_1 :
    FamilyRefutes Magma.srch10R806 [
      2503, 2530, 3068
    ] :=
  ⟨noS10R806_Law2503, noS10R806_Law2530, noS10R806_Law3068⟩
