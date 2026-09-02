import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 17 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 2,587 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3549 takes them (2298 nodes). -/
def ordS10R803_Law3549 : List (Fin 8) := [6, 7, 2, 0, 4, 1, 3, 5]

/-- No member of the class satisfies equation 3549. -/
theorem noS10R803_Law3549 : ∀ v : Magma.tup10R803,
    ¬ @Equation3549 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3723 takes them (143 nodes). -/
def ordS10R803_Law3723 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3723. -/
theorem noS10R803_Law3723 : ∀ v : Magma.tup10R803,
    ¬ @Equation3723 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3723) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3723) (by native_decide) v.1 v.2
    ((@Law3723.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3803 takes them (146 nodes). -/
def ordS10R803_Law3803 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3803. -/
theorem noS10R803_Law3803 : ∀ v : Magma.tup10R803,
    ¬ @Equation3803 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3803) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3803) (by native_decide) v.1 v.2
    ((@Law3803.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R803_refutes_16 :
    FamilyRefutes Magma.srch10R803 [
      3549, 3723, 3803
    ] :=
  ⟨noS10R803_Law3549, noS10R803_Law3723, noS10R803_Law3803⟩
