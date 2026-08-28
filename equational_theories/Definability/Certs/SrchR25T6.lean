import equational_theories.Definability.Srch_SR25

/-!
# Structural certificate targets: `Magma.srchR25` (part 7 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `8`
equations here, 839 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4583 takes them (141 nodes). -/
def ordSR25_Law4583 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4583. -/
theorem noSR25_Law4583 : ∀ v : Magma.tupR25,
    ¬ @Equation4583 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4583) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law4583) (by native_decide) v.1 v.2
    ((@Law4583.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4590 takes them (246 nodes). -/
def ordSR25_Law4590 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4590. -/
theorem noSR25_Law4590 : ∀ v : Magma.tupR25,
    ¬ @Equation4590 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4590) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law4590) (by native_decide) v.1 v.2
    ((@Law4590.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4597 takes them (58 nodes). -/
def ordSR25_Law4597 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4597. -/
theorem noSR25_Law4597 : ∀ v : Magma.tupR25,
    ¬ @Equation4597 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4597) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4597) (by native_decide) v.1 v.2
    ((@Law4597.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4601 takes them (64 nodes). -/
def ordSR25_Law4601 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4601. -/
theorem noSR25_Law4601 : ∀ v : Magma.tupR25,
    ¬ @Equation4601 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4601) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4601) (by native_decide) v.1 v.2
    ((@Law4601.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4603 takes them (59 nodes). -/
def ordSR25_Law4603 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4603. -/
theorem noSR25_Law4603 : ∀ v : Magma.tupR25,
    ¬ @Equation4603 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4603) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4603) (by native_decide) v.1 v.2
    ((@Law4603.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4611 takes them (92 nodes). -/
def ordSR25_Law4611 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4611. -/
theorem noSR25_Law4611 : ∀ v : Magma.tupR25,
    ¬ @Equation4611 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4611) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4611) (by native_decide) v.1 v.2
    ((@Law4611.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4619 takes them (79 nodes). -/
def ordSR25_Law4619 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4619. -/
theorem noSR25_Law4619 : ∀ v : Magma.tupR25,
    ¬ @Equation4619 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4619) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4619) (by native_decide) v.1 v.2
    ((@Law4619.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4622 takes them (100 nodes). -/
def ordSR25_Law4622 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4622. -/
theorem noSR25_Law4622 : ∀ v : Magma.tupR25,
    ¬ @Equation4622 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4622) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law4622) (by native_decide) v.1 v.2
    ((@Law4622.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srchR25_refutes_6 :
    FamilyRefutes Magma.srchR25 [
      4583, 4590, 4597, 4601, 4603, 4611, 4619, 4622
    ] :=
  ⟨noSR25_Law4583, noSR25_Law4590, noSR25_Law4597, noSR25_Law4601, noSR25_Law4603, noSR25_Law4611, noSR25_Law4619, noSR25_Law4622⟩
