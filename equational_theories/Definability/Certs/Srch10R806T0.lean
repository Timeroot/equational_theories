import equational_theories.Definability.Srch_S10R806

/-!
# Structural certificate targets: `Magma.srch10R806` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R806_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,617 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R806_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 429 takes them (1182 nodes). -/
def ordS10R806_Law429 : List (Fin 10) := [6, 5, 8, 3, 9, 7, 4, 2, 0, 1]

/-- No member of the class satisfies equation 429. -/
theorem noS10R806_Law429 : ∀ v : Magma.tup10R806,
    ¬ @Equation429 (Fin 10) (Magma.srch10R806 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law429) (E := S10R806.E) (tr := S10R806.tr) (z := S10R806.z)
    (st := S10R806.st) (X := S10R806.X) (envs := Magma.envsRed 10 S10R806.E 2)
    (ord := ordS10R806_Law429) (by native_decide) v.1 v.2
    ((@Law429.models_iff (Fin 10) (Magma.srch10R806 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1023 takes them (1823 nodes). -/
def ordS10R806_Law1023 : List (Fin 10) := [4, 0, 8, 2, 9, 7, 5, 6, 1, 3]

/-- No member of the class satisfies equation 1023. -/
theorem noS10R806_Law1023 : ∀ v : Magma.tup10R806,
    ¬ @Equation1023 (Fin 10) (Magma.srch10R806 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1023) (E := S10R806.E) (tr := S10R806.tr) (z := S10R806.z)
    (st := S10R806.st) (X := S10R806.X) (envs := Magma.envsRed 10 S10R806.E 2)
    (ord := ordS10R806_Law1023) (by native_decide) v.1 v.2
    ((@Law1023.models_iff (Fin 10) (Magma.srch10R806 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1026 takes them (612 nodes). -/
def ordS10R806_Law1026 : List (Fin 10) := [1, 5, 9, 8, 2, 6, 7, 0, 3, 4]

/-- No member of the class satisfies equation 1026. -/
theorem noS10R806_Law1026 : ∀ v : Magma.tup10R806,
    ¬ @Equation1026 (Fin 10) (Magma.srch10R806 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1026) (E := S10R806.E) (tr := S10R806.tr) (z := S10R806.z)
    (st := S10R806.st) (X := S10R806.X) (envs := Magma.envsRed 10 S10R806.E 2)
    (ord := ordS10R806_Law1026) (by native_decide) v.1 v.2
    ((@Law1026.models_iff (Fin 10) (Magma.srch10R806 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R806_refutes_0 :
    FamilyRefutes Magma.srch10R806 [
      429, 1023, 1026
    ] :=
  ⟨noS10R806_Law429, noS10R806_Law1023, noS10R806_Law1026⟩
