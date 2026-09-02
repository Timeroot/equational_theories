import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 29 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,681 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4480 takes them (1495 nodes). -/
def ordS10R803_Law4480 : List (Fin 8) := [3, 7, 6, 2, 1, 4, 5, 0]

/-- No member of the class satisfies equation 4480. -/
theorem noS10R803_Law4480 : ∀ v : Magma.tup10R803,
    ¬ @Equation4480 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4480) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4480) (by native_decide) v.1 v.2
    ((@Law4480.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4584 takes them (2186 nodes). -/
def ordS10R803_Law4584 : List (Fin 8) := [5, 0, 3, 7, 6, 1, 4, 2]

/-- No member of the class satisfies equation 4584. -/
theorem noS10R803_Law4584 : ∀ v : Magma.tup10R803,
    ¬ @Equation4584 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4584) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4584) (by native_decide) v.1 v.2
    ((@Law4584.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R803_refutes_28 :
    FamilyRefutes Magma.srch10R803 [
      4480, 4584
    ] :=
  ⟨noS10R803_Law4480, noS10R803_Law4584⟩
