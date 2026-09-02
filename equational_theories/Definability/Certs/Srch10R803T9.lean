import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 10 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 3,365 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2476 takes them (1017 nodes). -/
def ordS10R803_Law2476 : List (Fin 8) := [1, 0, 2, 3, 6, 7, 5, 4]

/-- No member of the class satisfies equation 2476. -/
theorem noS10R803_Law2476 : ∀ v : Magma.tup10R803,
    ¬ @Equation2476 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2476) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2476) (by native_decide) v.1 v.2
    ((@Law2476.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2480 takes them (489 nodes). -/
def ordS10R803_Law2480 : List (Fin 8) := [1, 2, 4, 7, 6, 0, 3, 5]

/-- No member of the class satisfies equation 2480. -/
theorem noS10R803_Law2480 : ∀ v : Magma.tup10R803,
    ¬ @Equation2480 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2480) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2480) (by native_decide) v.1 v.2
    ((@Law2480.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2484 takes them (439 nodes). -/
def ordS10R803_Law2484 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2484. -/
theorem noS10R803_Law2484 : ∀ v : Magma.tup10R803,
    ¬ @Equation2484 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2484) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2484) (by native_decide) v.1 v.2
    ((@Law2484.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2488 takes them (394 nodes). -/
def ordS10R803_Law2488 : List (Fin 8) := [0, 6, 7, 3, 5, 4, 1, 2]

/-- No member of the class satisfies equation 2488. -/
theorem noS10R803_Law2488 : ∀ v : Magma.tup10R803,
    ¬ @Equation2488 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2488) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law2488) (by native_decide) v.1 v.2
    ((@Law2488.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2517 takes them (186 nodes). -/
def ordS10R803_Law2517 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2517. -/
theorem noS10R803_Law2517 : ∀ v : Magma.tup10R803,
    ¬ @Equation2517 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2517) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2517) (by native_decide) v.1 v.2
    ((@Law2517.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2554 takes them (300 nodes). -/
def ordS10R803_Law2554 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2554. -/
theorem noS10R803_Law2554 : ∀ v : Magma.tup10R803,
    ¬ @Equation2554 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2554) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2554) (by native_decide) v.1 v.2
    ((@Law2554.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2623 takes them (183 nodes). -/
def ordS10R803_Law2623 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2623. -/
theorem noS10R803_Law2623 : ∀ v : Magma.tup10R803,
    ¬ @Equation2623 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2623) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 4)
    (ord := ordS10R803_Law2623) (by native_decide) v.1 v.2
    ((@Law2623.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2665 takes them (357 nodes). -/
def ordS10R803_Law2665 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2665. -/
theorem noS10R803_Law2665 : ∀ v : Magma.tup10R803,
    ¬ @Equation2665 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2665) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2665) (by native_decide) v.1 v.2
    ((@Law2665.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch10R803_refutes_9 :
    FamilyRefutes Magma.srch10R803 [
      2476, 2480, 2484, 2488, 2517, 2554, 2623, 2665
    ] :=
  ⟨noS10R803_Law2476, noS10R803_Law2480, noS10R803_Law2484, noS10R803_Law2488, noS10R803_Law2517, noS10R803_Law2554, noS10R803_Law2623, noS10R803_Law2665⟩
