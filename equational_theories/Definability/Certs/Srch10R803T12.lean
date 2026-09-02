import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 13 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,672 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3322 takes them (805 nodes). -/
def ordS10R803_Law3322 : List (Fin 8) := [0, 7, 1, 6, 5, 4, 2, 3]

/-- No member of the class satisfies equation 3322. -/
theorem noS10R803_Law3322 : ∀ v : Magma.tup10R803,
    ¬ @Equation3322 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3322) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3322) (by native_decide) v.1 v.2
    ((@Law3322.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3458 takes them (2471 nodes). -/
def ordS10R803_Law3458 : List (Fin 8) := [1, 7, 3, 0, 2, 6, 4, 5]

/-- No member of the class satisfies equation 3458. -/
theorem noS10R803_Law3458 : ∀ v : Magma.tup10R803,
    ¬ @Equation3458 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3458) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3458) (by native_decide) v.1 v.2
    ((@Law3458.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3460 takes them (396 nodes). -/
def ordS10R803_Law3460 : List (Fin 8) := [6, 2, 7, 3, 1, 0, 5, 4]

/-- No member of the class satisfies equation 3460. -/
theorem noS10R803_Law3460 : ∀ v : Magma.tup10R803,
    ¬ @Equation3460 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3460) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3460) (by native_decide) v.1 v.2
    ((@Law3460.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R803_refutes_12 :
    FamilyRefutes Magma.srch10R803 [
      3322, 3458, 3460
    ] :=
  ⟨noS10R803_Law3322, noS10R803_Law3458, noS10R803_Law3460⟩
