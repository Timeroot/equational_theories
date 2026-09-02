import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 21 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,656 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3935 takes them (388 nodes). -/
def ordS10R803_Law3935 : List (Fin 8) := [0, 2, 1, 6, 7, 3, 4, 5]

/-- No member of the class satisfies equation 3935. -/
theorem noS10R803_Law3935 : ∀ v : Magma.tup10R803,
    ¬ @Equation3935 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3935) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3935) (by native_decide) v.1 v.2
    ((@Law3935.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (2780 nodes). -/
def ordS10R803_Law3955 : List (Fin 8) := [2, 0, 1, 3, 6, 5, 7, 4]

/-- No member of the class satisfies equation 3955. -/
theorem noS10R803_Law3955 : ∀ v : Magma.tup10R803,
    ¬ @Equation3955 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4104 takes them (488 nodes). -/
def ordS10R803_Law4104 : List (Fin 8) := [1, 3, 6, 0, 2, 7, 5, 4]

/-- No member of the class satisfies equation 4104. -/
theorem noS10R803_Law4104 : ∀ v : Magma.tup10R803,
    ¬ @Equation4104 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4104) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law4104) (by native_decide) v.1 v.2
    ((@Law4104.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R803_refutes_20 :
    FamilyRefutes Magma.srch10R803 [
      3935, 3955, 4104
    ] :=
  ⟨noS10R803_Law3935, noS10R803_Law3955, noS10R803_Law4104⟩
