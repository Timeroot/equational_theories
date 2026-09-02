import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 28 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,323 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4436 takes them (1350 nodes). -/
def ordS10R803_Law4436 : List (Fin 8) := [3, 1, 0, 2, 5, 7, 6, 4]

/-- No member of the class satisfies equation 4436. -/
theorem noS10R803_Law4436 : ∀ v : Magma.tup10R803,
    ¬ @Equation4436 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4436) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4436) (by native_decide) v.1 v.2
    ((@Law4436.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4445 takes them (1107 nodes). -/
def ordS10R803_Law4445 : List (Fin 8) := [3, 6, 1, 7, 2, 4, 0, 5]

/-- No member of the class satisfies equation 4445. -/
theorem noS10R803_Law4445 : ∀ v : Magma.tup10R803,
    ¬ @Equation4445 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4445) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4445) (by native_decide) v.1 v.2
    ((@Law4445.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4472 takes them (866 nodes). -/
def ordS10R803_Law4472 : List (Fin 8) := [1, 0, 3, 6, 7, 2, 5, 4]

/-- No member of the class satisfies equation 4472. -/
theorem noS10R803_Law4472 : ∀ v : Magma.tup10R803,
    ¬ @Equation4472 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4472) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4472) (by native_decide) v.1 v.2
    ((@Law4472.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R803_refutes_27 :
    FamilyRefutes Magma.srch10R803 [
      4436, 4445, 4472
    ] :=
  ⟨noS10R803_Law4436, noS10R803_Law4445, noS10R803_Law4472⟩
