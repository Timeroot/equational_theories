import equational_theories.Definability.Srch_S10R400

/-!
# Structural certificate targets: `Magma.srch10R400` (part 2 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R400_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 3,719 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R400_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3342 takes them (400 nodes). -/
def ordS10R400_Law3342 : List (Fin 11) := [8, 7, 3, 0, 5, 10, 9, 6, 4, 2, 1]

/-- No member of the class satisfies equation 3342. -/
theorem noS10R400_Law3342 : ∀ v : Magma.tup10R400,
    ¬ @Equation3342 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3342) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law3342) (by native_decide) v.1 v.2
    ((@Law3342.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3350 takes them (278 nodes). -/
def ordS10R400_Law3350 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3350. -/
theorem noS10R400_Law3350 : ∀ v : Magma.tup10R400,
    ¬ @Equation3350 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3350) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 3)
    (ord := ordS10R400_Law3350) (by native_decide) v.1 v.2
    ((@Law3350.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3545 takes them (1534 nodes). -/
def ordS10R400_Law3545 : List (Fin 11) := [3, 2, 7, 9, 6, 4, 5, 8, 10, 0, 1]

/-- No member of the class satisfies equation 3545. -/
theorem noS10R400_Law3545 : ∀ v : Magma.tup10R400,
    ¬ @Equation3545 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3545) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law3545) (by native_decide) v.1 v.2
    ((@Law3545.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3558 takes them (1507 nodes). -/
def ordS10R400_Law3558 : List (Fin 11) := [3, 1, 6, 2, 8, 0, 5, 7, 9, 4, 10]

/-- No member of the class satisfies equation 3558. -/
theorem noS10R400_Law3558 : ∀ v : Magma.tup10R400,
    ¬ @Equation3558 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3558) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law3558) (by native_decide) v.1 v.2
    ((@Law3558.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch10R400_refutes_1 :
    FamilyRefutes Magma.srch10R400 [
      3342, 3350, 3545, 3558
    ] :=
  ⟨noS10R400_Law3342, noS10R400_Law3350, noS10R400_Law3545, noS10R400_Law3558⟩
