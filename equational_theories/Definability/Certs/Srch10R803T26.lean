import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 27 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,635 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4406 takes them (1240 nodes). -/
def ordS10R803_Law4406 : List (Fin 8) := [5, 0, 6, 7, 3, 2, 1, 4]

/-- No member of the class satisfies equation 4406. -/
theorem noS10R803_Law4406 : ∀ v : Magma.tup10R803,
    ¬ @Equation4406 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4406) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4406) (by native_decide) v.1 v.2
    ((@Law4406.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4432 takes them (1088 nodes). -/
def ordS10R803_Law4432 : List (Fin 8) := [0, 1, 4, 3, 7, 6, 2, 5]

/-- No member of the class satisfies equation 4432. -/
theorem noS10R803_Law4432 : ∀ v : Magma.tup10R803,
    ¬ @Equation4432 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4432) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4432) (by native_decide) v.1 v.2
    ((@Law4432.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4433 takes them (1307 nodes). -/
def ordS10R803_Law4433 : List (Fin 8) := [6, 2, 3, 7, 1, 5, 0, 4]

/-- No member of the class satisfies equation 4433. -/
theorem noS10R803_Law4433 : ∀ v : Magma.tup10R803,
    ¬ @Equation4433 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4433) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4433) (by native_decide) v.1 v.2
    ((@Law4433.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R803_refutes_26 :
    FamilyRefutes Magma.srch10R803 [
      4406, 4432, 4433
    ] :=
  ⟨noS10R803_Law4406, noS10R803_Law4432, noS10R803_Law4433⟩
