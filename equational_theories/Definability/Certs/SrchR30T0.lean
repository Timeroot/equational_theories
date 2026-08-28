import equational_theories.Definability.Srch_SR30

/-!
# Structural certificate targets: `Magma.srchR30` (part 1 of 28)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR30_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `6`
equations here, 2,519 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR30_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 50 takes them (114 nodes). -/
def ordSR30_Law50 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 50. -/
theorem noSR30_Law50 : ∀ v : Magma.tupR30,
    ¬ @Equation50 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law50) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law50) (by native_decide) v.1 v.2
    ((@Law50.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 102 takes them (105 nodes). -/
def ordSR30_Law102 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 102. -/
theorem noSR30_Law102 : ∀ v : Magma.tupR30,
    ¬ @Equation102 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law102) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law102) (by native_decide) v.1 v.2
    ((@Law102.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 104 takes them (1053 nodes). -/
def ordSR30_Law104 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 104. -/
theorem noSR30_Law104 : ∀ v : Magma.tupR30,
    ¬ @Equation104 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law104) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law104) (by native_decide) v.1 v.2
    ((@Law104.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 205 takes them (1059 nodes). -/
def ordSR30_Law205 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 205. -/
theorem noSR30_Law205 : ∀ v : Magma.tupR30,
    ¬ @Equation205 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law205) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law205) (by native_decide) v.1 v.2
    ((@Law205.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 228 takes them (89 nodes). -/
def ordSR30_Law228 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 228. -/
theorem noSR30_Law228 : ∀ v : Magma.tupR30,
    ¬ @Equation228 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law228) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law228) (by native_decide) v.1 v.2
    ((@Law228.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 280 takes them (99 nodes). -/
def ordSR30_Law280 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 280. -/
theorem noSR30_Law280 : ∀ v : Magma.tupR30,
    ¬ @Equation280 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law280) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law280) (by native_decide) v.1 v.2
    ((@Law280.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srchR30_refutes_0 :
    FamilyRefutes Magma.srchR30 [
      50, 102, 104, 205, 228, 280
    ] :=
  ⟨noSR30_Law50, noSR30_Law102, noSR30_Law104, noSR30_Law205, noSR30_Law228, noSR30_Law280⟩
