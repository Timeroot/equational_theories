import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 3 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 3,417 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 361 takes them (1162 nodes). -/
def ordS10R803_Law361 : List (Fin 8) := [1, 6, 2, 3, 7, 0, 4, 5]

/-- No member of the class satisfies equation 361. -/
theorem noS10R803_Law361 : ∀ v : Magma.tup10R803,
    ¬ @Equation361 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law361) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law361) (by native_decide) v.1 v.2
    ((@Law361.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 377 takes them (636 nodes). -/
def ordS10R803_Law377 : List (Fin 8) := [0, 7, 3, 1, 2, 6, 4, 5]

/-- No member of the class satisfies equation 377. -/
theorem noS10R803_Law377 : ∀ v : Magma.tup10R803,
    ¬ @Equation377 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law377) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law377) (by native_decide) v.1 v.2
    ((@Law377.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 426 takes them (967 nodes). -/
def ordS10R803_Law426 : List (Fin 8) := [3, 0, 4, 2, 6, 1, 7, 5]

/-- No member of the class satisfies equation 426. -/
theorem noS10R803_Law426 : ∀ v : Magma.tup10R803,
    ¬ @Equation426 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law426) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law426) (by native_decide) v.1 v.2
    ((@Law426.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 430 takes them (326 nodes). -/
def ordS10R803_Law430 : List (Fin 8) := [7, 0, 1, 2, 3, 5, 6, 4]

/-- No member of the class satisfies equation 430. -/
theorem noS10R803_Law430 : ∀ v : Magma.tup10R803,
    ¬ @Equation430 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 432 takes them (326 nodes). -/
def ordS10R803_Law432 : List (Fin 8) := [7, 2, 1, 0, 6, 4, 5, 3]

/-- No member of the class satisfies equation 432. -/
theorem noS10R803_Law432 : ∀ v : Magma.tup10R803,
    ¬ @Equation432 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law432) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law432) (by native_decide) v.1 v.2
    ((@Law432.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch10R803_refutes_2 :
    FamilyRefutes Magma.srch10R803 [
      361, 377, 426, 430, 432
    ] :=
  ⟨noS10R803_Law361, noS10R803_Law377, noS10R803_Law426, noS10R803_Law430, noS10R803_Law432⟩
