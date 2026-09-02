import equational_theories.Definability.Srch_S10R400

/-!
# Structural certificate targets: `Magma.srch10R400` (part 1 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R400_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,441 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R400_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 43 takes them (1289 nodes). -/
def ordS10R400_Law43 : List (Fin 11) := [2, 9, 10, 5, 8, 1, 4, 7, 6, 0, 3]

/-- No member of the class satisfies equation 43. -/
theorem noS10R400_Law43 : ∀ v : Magma.tup10R400,
    ¬ @Equation43 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law43) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law43) (by native_decide) v.1 v.2
    ((@Law43.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 332 takes them (443 nodes). -/
def ordS10R400_Law332 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 332. -/
theorem noS10R400_Law332 : ∀ v : Magma.tup10R400,
    ¬ @Equation332 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law332) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law332) (by native_decide) v.1 v.2
    ((@Law332.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 387 takes them (348 nodes). -/
def ordS10R400_Law387 : List (Fin 11) := [6, 0, 10, 4, 5, 9, 3, 8, 1, 2, 7]

/-- No member of the class satisfies equation 387. -/
theorem noS10R400_Law387 : ∀ v : Magma.tup10R400,
    ¬ @Equation387 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law387) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law387) (by native_decide) v.1 v.2
    ((@Law387.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (1361 nodes). -/
def ordS10R400_Law3308 : List (Fin 11) := [3, 10, 7, 6, 5, 8, 0, 2, 9, 4, 1]

/-- No member of the class satisfies equation 3308. -/
theorem noS10R400_Law3308 : ∀ v : Magma.tup10R400,
    ¬ @Equation3308 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch10R400_refutes_0 :
    FamilyRefutes Magma.srch10R400 [
      43, 332, 387, 3308
    ] :=
  ⟨noS10R400_Law43, noS10R400_Law332, noS10R400_Law387, noS10R400_Law3308⟩
