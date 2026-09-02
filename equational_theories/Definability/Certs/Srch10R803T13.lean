import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 14 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 1,308 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3467 takes them (982 nodes). -/
def ordS10R803_Law3467 : List (Fin 8) := [0, 6, 7, 3, 1, 2, 5, 4]

/-- No member of the class satisfies equation 3467. -/
theorem noS10R803_Law3467 : ∀ v : Magma.tup10R803,
    ¬ @Equation3467 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3467) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3467) (by native_decide) v.1 v.2
    ((@Law3467.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3468 takes them (326 nodes). -/
def ordS10R803_Law3468 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3468. -/
theorem noS10R803_Law3468 : ∀ v : Magma.tup10R803,
    ¬ @Equation3468 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3468) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3468) (by native_decide) v.1 v.2
    ((@Law3468.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R803_refutes_13 :
    FamilyRefutes Magma.srch10R803 [
      3467, 3468
    ] :=
  ⟨noS10R803_Law3467, noS10R803_Law3468⟩
