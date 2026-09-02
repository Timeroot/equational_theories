import equational_theories.Definability.Srch_S10R400

/-!
# Structural certificate targets: `Magma.srch10R400` (part 4 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R400_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,111 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R400_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3964 takes them (2807 nodes). -/
def ordS10R400_Law3964 : List (Fin 11) := [6, 10, 1, 7, 5, 2, 3, 0, 9, 8, 4]

/-- No member of the class satisfies equation 3964. -/
theorem noS10R400_Law3964 : ∀ v : Magma.tup10R400,
    ¬ @Equation3964 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3964) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law3964) (by native_decide) v.1 v.2
    ((@Law3964.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3979 takes them (304 nodes). -/
def ordS10R400_Law3979 : List (Fin 11) := [6, 0, 5, 3, 10, 2, 7, 8, 4, 9, 1]

/-- No member of the class satisfies equation 3979. -/
theorem noS10R400_Law3979 : ∀ v : Magma.tup10R400,
    ¬ @Equation3979 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3979) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 3)
    (ord := ordS10R400_Law3979) (by native_decide) v.1 v.2
    ((@Law3979.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R400_refutes_3 :
    FamilyRefutes Magma.srch10R400 [
      3964, 3979
    ] :=
  ⟨noS10R400_Law3964, noS10R400_Law3979⟩
