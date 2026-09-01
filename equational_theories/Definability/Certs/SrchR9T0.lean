import equational_theories.Definability.Srch_SR9

/-!
# Structural certificate targets: `Magma.srchR9` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 3,519 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3273 takes them (223 nodes). -/
def ordSR9_Law3273 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3273. -/
theorem noSR9_Law3273 : ∀ v : Magma.tupR9,
    ¬ @Equation3273 (Fin 6) (Magma.srchR9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3273) (E := SR9.E) (tr := SR9.tr) (z := SR9.z)
    (st := SR9.st) (X := SR9.X) (envs := Magma.envsRed 6 SR9.E 3)
    (ord := ordSR9_Law3273) (by native_decide) v.1 v.2
    ((@Law3273.models_iff (Fin 6) (Magma.srchR9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3292 takes them (673 nodes). -/
def ordSR9_Law3292 : List (Fin 12) := [2, 3, 5, 8, 4, 1, 10, 11, 7, 0, 9, 6]

/-- No member of the class satisfies equation 3292. -/
theorem noSR9_Law3292 : ∀ v : Magma.tupR9,
    ¬ @Equation3292 (Fin 6) (Magma.srchR9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3292) (E := SR9.E) (tr := SR9.tr) (z := SR9.z)
    (st := SR9.st) (X := SR9.X) (envs := Magma.envsRed 6 SR9.E 3)
    (ord := ordSR9_Law3292) (by native_decide) v.1 v.2
    ((@Law3292.models_iff (Fin 6) (Magma.srchR9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3295 takes them (205 nodes). -/
def ordSR9_Law3295 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3295. -/
theorem noSR9_Law3295 : ∀ v : Magma.tupR9,
    ¬ @Equation3295 (Fin 6) (Magma.srchR9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3295) (E := SR9.E) (tr := SR9.tr) (z := SR9.z)
    (st := SR9.st) (X := SR9.X) (envs := Magma.envsRed 6 SR9.E 4)
    (ord := ordSR9_Law3295) (by native_decide) v.1 v.2
    ((@Law3295.models_iff (Fin 6) (Magma.srchR9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4077 takes them (807 nodes). -/
def ordSR9_Law4077 : List (Fin 12) := [1, 8, 3, 4, 11, 5, 6, 2, 7, 0, 9, 10]

/-- No member of the class satisfies equation 4077. -/
theorem noSR9_Law4077 : ∀ v : Magma.tupR9,
    ¬ @Equation4077 (Fin 6) (Magma.srchR9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4077) (E := SR9.E) (tr := SR9.tr) (z := SR9.z)
    (st := SR9.st) (X := SR9.X) (envs := Magma.envsRed 6 SR9.E 3)
    (ord := ordSR9_Law4077) (by native_decide) v.1 v.2
    ((@Law4077.models_iff (Fin 6) (Magma.srchR9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4102 takes them (295 nodes). -/
def ordSR9_Law4102 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4102. -/
theorem noSR9_Law4102 : ∀ v : Magma.tupR9,
    ¬ @Equation4102 (Fin 6) (Magma.srchR9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4102) (E := SR9.E) (tr := SR9.tr) (z := SR9.z)
    (st := SR9.st) (X := SR9.X) (envs := Magma.envsRed 6 SR9.E 3)
    (ord := ordSR9_Law4102) (by native_decide) v.1 v.2
    ((@Law4102.models_iff (Fin 6) (Magma.srchR9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4114 takes them (265 nodes). -/
def ordSR9_Law4114 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4114. -/
theorem noSR9_Law4114 : ∀ v : Magma.tupR9,
    ¬ @Equation4114 (Fin 6) (Magma.srchR9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4114) (E := SR9.E) (tr := SR9.tr) (z := SR9.z)
    (st := SR9.st) (X := SR9.X) (envs := Magma.envsRed 6 SR9.E 4)
    (ord := ordSR9_Law4114) (by native_decide) v.1 v.2
    ((@Law4114.models_iff (Fin 6) (Magma.srchR9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4490 takes them (1051 nodes). -/
def ordSR9_Law4490 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4490. -/
theorem noSR9_Law4490 : ∀ v : Magma.tupR9,
    ¬ @Equation4490 (Fin 6) (Magma.srchR9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4490) (E := SR9.E) (tr := SR9.tr) (z := SR9.z)
    (st := SR9.st) (X := SR9.X) (envs := Magma.envsRed 6 SR9.E 3)
    (ord := ordSR9_Law4490) (by native_decide) v.1 v.2
    ((@Law4490.models_iff (Fin 6) (Magma.srchR9 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srchR9_refutes_0 :
    FamilyRefutes Magma.srchR9 [
      3273, 3292, 3295, 4077, 4102, 4114, 4490
    ] :=
  ⟨noSR9_Law3273, noSR9_Law3292, noSR9_Law3295, noSR9_Law4077, noSR9_Law4102, noSR9_Law4114, noSR9_Law4490⟩
