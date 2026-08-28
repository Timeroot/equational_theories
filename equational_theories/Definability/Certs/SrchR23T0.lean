import equational_theories.Definability.Srch_SR23

/-!
# Structural certificate targets: `Magma.srchR23`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR23_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `10`
equations here, 1,986 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR23_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3364 takes them (236 nodes). -/
def ordSR23_Law3364 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3364. -/
theorem noSR23_Law3364 : ∀ v : Magma.tupR23,
    ¬ @Equation3364 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3364) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law3364) (by native_decide) v.1 v.2
    ((@Law3364.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3370 takes them (212 nodes). -/
def ordSR23_Law3370 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3370. -/
theorem noSR23_Law3370 : ∀ v : Magma.tupR23,
    ¬ @Equation3370 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3370) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law3370) (by native_decide) v.1 v.2
    ((@Law3370.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3553 takes them (196 nodes). -/
def ordSR23_Law3553 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3553. -/
theorem noSR23_Law3553 : ∀ v : Magma.tupR23,
    ¬ @Equation3553 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3553) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law3553) (by native_decide) v.1 v.2
    ((@Law3553.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3567 takes them (211 nodes). -/
def ordSR23_Law3567 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3567. -/
theorem noSR23_Law3567 : ∀ v : Magma.tupR23,
    ¬ @Equation3567 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3567) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law3567) (by native_decide) v.1 v.2
    ((@Law3567.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3737 takes them (230 nodes). -/
def ordSR23_Law3737 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3737. -/
theorem noSR23_Law3737 : ∀ v : Magma.tupR23,
    ¬ @Equation3737 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3737) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law3737) (by native_decide) v.1 v.2
    ((@Law3737.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3794 takes them (186 nodes). -/
def ordSR23_Law3794 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3794. -/
theorem noSR23_Law3794 : ∀ v : Magma.tupR23,
    ¬ @Equation3794 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3794) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law3794) (by native_decide) v.1 v.2
    ((@Law3794.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4013 takes them (207 nodes). -/
def ordSR23_Law4013 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4013. -/
theorem noSR23_Law4013 : ∀ v : Magma.tupR23,
    ¬ @Equation4013 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4013) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law4013) (by native_decide) v.1 v.2
    ((@Law4013.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4026 takes them (152 nodes). -/
def ordSR23_Law4026 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4026. -/
theorem noSR23_Law4026 : ∀ v : Magma.tupR23,
    ¬ @Equation4026 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4026) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law4026) (by native_decide) v.1 v.2
    ((@Law4026.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4182 takes them (201 nodes). -/
def ordSR23_Law4182 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4182. -/
theorem noSR23_Law4182 : ∀ v : Magma.tupR23,
    ¬ @Equation4182 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4182) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law4182) (by native_decide) v.1 v.2
    ((@Law4182.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4216 takes them (155 nodes). -/
def ordSR23_Law4216 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4216. -/
theorem noSR23_Law4216 : ∀ v : Magma.tupR23,
    ¬ @Equation4216 (Fin 6) (Magma.srchR23 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4216) (E := SR23.E) (tr := SR23.tr) (z := SR23.z)
    (st := SR23.st) (X := SR23.X) (envs := Magma.envsRed 6 SR23.E 3)
    (ord := ordSR23_Law4216) (by native_decide) v.1 v.2
    ((@Law4216.models_iff (Fin 6) (Magma.srchR23 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srchR23_refutes_0 :
    FamilyRefutes Magma.srchR23 [
      3364, 3370, 3553, 3567, 3737, 3794, 4013, 4026, 4182, 4216
    ] :=
  ⟨noSR23_Law3364, noSR23_Law3370, noSR23_Law3553, noSR23_Law3567, noSR23_Law3737, noSR23_Law3794, noSR23_Law4013, noSR23_Law4026, noSR23_Law4182, noSR23_Law4216⟩
