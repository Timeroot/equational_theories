import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 4 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,568 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 838 takes them (357 nodes). -/
def ordS10R803_Law838 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 838. -/
theorem noS10R803_Law838 : ∀ v : Magma.tup10R803,
    ¬ @Equation838 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law838) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law838) (by native_decide) v.1 v.2
    ((@Law838.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1025 takes them (1911 nodes). -/
def ordS10R803_Law1025 : List (Fin 8) := [0, 4, 1, 2, 7, 6, 3, 5]

/-- No member of the class satisfies equation 1025. -/
theorem noS10R803_Law1025 : ∀ v : Magma.tup10R803,
    ¬ @Equation1025 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1025) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law1025) (by native_decide) v.1 v.2
    ((@Law1025.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1031 takes them (1300 nodes). -/
def ordS10R803_Law1031 : List (Fin 8) := [1, 3, 0, 2, 4, 6, 7, 5]

/-- No member of the class satisfies equation 1031. -/
theorem noS10R803_Law1031 : ∀ v : Magma.tup10R803,
    ¬ @Equation1031 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1031) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1031) (by native_decide) v.1 v.2
    ((@Law1031.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R803_refutes_3 :
    FamilyRefutes Magma.srch10R803 [
      838, 1025, 1031
    ] :=
  ⟨noS10R803_Law838, noS10R803_Law1025, noS10R803_Law1031⟩
