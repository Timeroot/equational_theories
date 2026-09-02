import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 19 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 2,063 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3873 takes them (1272 nodes). -/
def ordS10R803_Law3873 : List (Fin 8) := [0, 3, 2, 5, 1, 6, 7, 4]

/-- No member of the class satisfies equation 3873. -/
theorem noS10R803_Law3873 : ∀ v : Magma.tup10R803,
    ¬ @Equation3873 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3873) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3873) (by native_decide) v.1 v.2
    ((@Law3873.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3897 takes them (465 nodes). -/
def ordS10R803_Law3897 : List (Fin 8) := [6, 4, 0, 2, 3, 7, 5, 1]

/-- No member of the class satisfies equation 3897. -/
theorem noS10R803_Law3897 : ∀ v : Magma.tup10R803,
    ¬ @Equation3897 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3897) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3897) (by native_decide) v.1 v.2
    ((@Law3897.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3901 takes them (326 nodes). -/
def ordS10R803_Law3901 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3901. -/
theorem noS10R803_Law3901 : ∀ v : Magma.tup10R803,
    ¬ @Equation3901 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3901) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law3901) (by native_decide) v.1 v.2
    ((@Law3901.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R803_refutes_18 :
    FamilyRefutes Magma.srch10R803 [
      3873, 3897, 3901
    ] :=
  ⟨noS10R803_Law3873, noS10R803_Law3897, noS10R803_Law3901⟩
