import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 15 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,242 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3511 takes them (2822 nodes). -/
def ordS10R803_Law3511 : List (Fin 8) := [6, 0, 1, 3, 2, 5, 7, 4]

/-- No member of the class satisfies equation 3511. -/
theorem noS10R803_Law3511 : ∀ v : Magma.tup10R803,
    ¬ @Equation3511 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3525 takes them (420 nodes). -/
def ordS10R803_Law3525 : List (Fin 8) := [1, 7, 2, 6, 0, 3, 4, 5]

/-- No member of the class satisfies equation 3525. -/
theorem noS10R803_Law3525 : ∀ v : Magma.tup10R803,
    ¬ @Equation3525 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3525) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3525) (by native_decide) v.1 v.2
    ((@Law3525.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R803_refutes_14 :
    FamilyRefutes Magma.srch10R803 [
      3511, 3525
    ] :=
  ⟨noS10R803_Law3511, noS10R803_Law3525⟩
