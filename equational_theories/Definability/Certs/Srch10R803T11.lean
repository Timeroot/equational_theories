import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 12 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 3,642 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3316 takes them (3642 nodes). -/
def ordS10R803_Law3316 : List (Fin 8) := [5, 3, 0, 2, 6, 1, 7, 4]

/-- No member of the class satisfies equation 3316. -/
theorem noS10R803_Law3316 : ∀ v : Magma.tup10R803,
    ¬ @Equation3316 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3316) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3316) (by native_decide) v.1 v.2
    ((@Law3316.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch10R803_refutes_11 :
    FamilyRefutes Magma.srch10R803 [
      3316
    ] :=
  noS10R803_Law3316
