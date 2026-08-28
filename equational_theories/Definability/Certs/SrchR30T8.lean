import equational_theories.Definability.Srch_SR30

/-!
# Structural certificate targets: `Magma.srchR30` (part 9 of 28)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR30_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 3,701 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR30_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2050 takes them (864 nodes). -/
def ordSR30_Law2050 : List (Fin 10) := [2, 1, 0, 4, 8, 5, 7, 3, 6, 9]

/-- No member of the class satisfies equation 2050. -/
theorem noSR30_Law2050 : ∀ v : Magma.tupR30,
    ¬ @Equation2050 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2050) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law2050) (by native_decide) v.1 v.2
    ((@Law2050.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2240 takes them (1139 nodes). -/
def ordSR30_Law2240 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2240. -/
theorem noSR30_Law2240 : ∀ v : Magma.tupR30,
    ¬ @Equation2240 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2240) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law2240) (by native_decide) v.1 v.2
    ((@Law2240.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2243 takes them (1698 nodes). -/
def ordSR30_Law2243 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2243. -/
theorem noSR30_Law2243 : ∀ v : Magma.tupR30,
    ¬ @Equation2243 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2243) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law2243) (by native_decide) v.1 v.2
    ((@Law2243.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srchR30_refutes_8 :
    FamilyRefutes Magma.srchR30 [
      2050, 2240, 2243
    ] :=
  ⟨noSR30_Law2050, noSR30_Law2240, noSR30_Law2243⟩
