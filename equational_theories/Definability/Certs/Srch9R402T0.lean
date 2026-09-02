import equational_theories.Definability.Srch_S9R402

/-!
# Structural certificate targets: `Magma.srch9R402`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R402_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 1,380 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R402_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1444 takes them (387 nodes). -/
def ordS9R402_Law1444 : List (Fin 7) := [6, 2, 4, 3, 0, 5, 1]

/-- No member of the class satisfies equation 1444. -/
theorem noS9R402_Law1444 : ∀ v : Magma.tup9R402,
    ¬ @Equation1444 (Fin 9) (Magma.srch9R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S9R402.E) (tr := S9R402.tr) (z := S9R402.z)
    (st := S9R402.st) (X := S9R402.X) (envs := Magma.envsRed 9 S9R402.E 2)
    (ord := ordS9R402_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 9) (Magma.srch9R402 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (181 nodes). -/
def ordS9R402_Law2053 : List (Fin 7) := [5, 6, 3, 4, 0, 1, 2]

/-- No member of the class satisfies equation 2053. -/
theorem noS9R402_Law2053 : ∀ v : Magma.tup9R402,
    ¬ @Equation2053 (Fin 9) (Magma.srch9R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S9R402.E) (tr := S9R402.tr) (z := S9R402.z)
    (st := S9R402.st) (X := S9R402.X) (envs := Magma.envsRed 9 S9R402.E 2)
    (ord := ordS9R402_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 9) (Magma.srch9R402 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3556 takes them (253 nodes). -/
def ordS9R402_Law3556 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3556. -/
theorem noS9R402_Law3556 : ∀ v : Magma.tup9R402,
    ¬ @Equation3556 (Fin 9) (Magma.srch9R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S9R402.E) (tr := S9R402.tr) (z := S9R402.z)
    (st := S9R402.st) (X := S9R402.X) (envs := Magma.envsRed 9 S9R402.E 2)
    (ord := ordS9R402_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 9) (Magma.srch9R402 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3924 takes them (355 nodes). -/
def ordS9R402_Law3924 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3924. -/
theorem noS9R402_Law3924 : ∀ v : Magma.tup9R402,
    ¬ @Equation3924 (Fin 9) (Magma.srch9R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S9R402.E) (tr := S9R402.tr) (z := S9R402.z)
    (st := S9R402.st) (X := S9R402.X) (envs := Magma.envsRed 9 S9R402.E 2)
    (ord := ordS9R402_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 9) (Magma.srch9R402 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4358 takes them (88 nodes). -/
def ordS9R402_Law4358 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4358. -/
theorem noS9R402_Law4358 : ∀ v : Magma.tup9R402,
    ¬ @Equation4358 (Fin 9) (Magma.srch9R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := S9R402.E) (tr := S9R402.tr) (z := S9R402.z)
    (st := S9R402.st) (X := S9R402.X) (envs := Magma.envsRed 9 S9R402.E 3)
    (ord := ordS9R402_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 9) (Magma.srch9R402 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4544 takes them (40 nodes). -/
def ordS9R402_Law4544 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4544. -/
theorem noS9R402_Law4544 : ∀ v : Magma.tup9R402,
    ¬ @Equation4544 (Fin 9) (Magma.srch9R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4544) (E := S9R402.E) (tr := S9R402.tr) (z := S9R402.z)
    (st := S9R402.st) (X := S9R402.X) (envs := Magma.envsRed 9 S9R402.E 3)
    (ord := ordS9R402_Law4544) (by native_decide) v.1 v.2
    ((@Law4544.models_iff (Fin 9) (Magma.srch9R402 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4677 takes them (76 nodes). -/
def ordS9R402_Law4677 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4677. -/
theorem noS9R402_Law4677 : ∀ v : Magma.tup9R402,
    ¬ @Equation4677 (Fin 9) (Magma.srch9R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4677) (E := S9R402.E) (tr := S9R402.tr) (z := S9R402.z)
    (st := S9R402.st) (X := S9R402.X) (envs := Magma.envsRed 9 S9R402.E 3)
    (ord := ordS9R402_Law4677) (by native_decide) v.1 v.2
    ((@Law4677.models_iff (Fin 9) (Magma.srch9R402 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch9R402_refutes_0 :
    FamilyRefutes Magma.srch9R402 [
      1444, 2053, 3556, 3924, 4358, 4544, 4677
    ] :=
  ⟨noS9R402_Law1444, noS9R402_Law2053, noS9R402_Law3556, noS9R402_Law3924, noS9R402_Law4358, noS9R402_Law4544, noS9R402_Law4677⟩
