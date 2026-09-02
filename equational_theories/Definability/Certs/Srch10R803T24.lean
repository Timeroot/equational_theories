import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 25 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,667 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4316 takes them (1921 nodes). -/
def ordS10R803_Law4316 : List (Fin 8) := [2, 6, 7, 0, 1, 5, 4, 3]

/-- No member of the class satisfies equation 4316. -/
theorem noS10R803_Law4316 : ∀ v : Magma.tup10R803,
    ¬ @Equation4316 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4316) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law4316) (by native_decide) v.1 v.2
    ((@Law4316.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4318 takes them (746 nodes). -/
def ordS10R803_Law4318 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4318. -/
theorem noS10R803_Law4318 : ∀ v : Magma.tup10R803,
    ¬ @Equation4318 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4318) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law4318) (by native_decide) v.1 v.2
    ((@Law4318.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R803_refutes_24 :
    FamilyRefutes Magma.srch10R803 [
      4316, 4318
    ] :=
  ⟨noS10R803_Law4316, noS10R803_Law4318⟩
