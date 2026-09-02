import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 20 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,836 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3917 takes them (2157 nodes). -/
def ordS10R803_Law3917 : List (Fin 8) := [2, 7, 6, 3, 0, 4, 1, 5]

/-- No member of the class satisfies equation 3917. -/
theorem noS10R803_Law3917 : ∀ v : Magma.tup10R803,
    ¬ @Equation3917 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3927 takes them (1679 nodes). -/
def ordS10R803_Law3927 : List (Fin 8) := [0, 7, 5, 6, 1, 3, 2, 4]

/-- No member of the class satisfies equation 3927. -/
theorem noS10R803_Law3927 : ∀ v : Magma.tup10R803,
    ¬ @Equation3927 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3927) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law3927) (by native_decide) v.1 v.2
    ((@Law3927.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R803_refutes_19 :
    FamilyRefutes Magma.srch10R803 [
      3917, 3927
    ] :=
  ⟨noS10R803_Law3917, noS10R803_Law3927⟩
