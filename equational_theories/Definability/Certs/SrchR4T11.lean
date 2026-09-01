import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 12 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 3,222 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3296 takes them (1508 nodes). -/
def ordSR4_Law3296 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3296. -/
theorem noSR4_Law3296 : ∀ v : Magma.tupR4,
    ¬ @Equation3296 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3296) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3296) (by native_decide) v.1 v.2
    ((@Law3296.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3300 takes them (453 nodes). -/
def ordSR4_Law3300 : List (Fin 12) := [11, 7, 0, 5, 8, 6, 4, 9, 3, 1, 2, 10]

/-- No member of the class satisfies equation 3300. -/
theorem noSR4_Law3300 : ∀ v : Magma.tupR4,
    ¬ @Equation3300 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3300) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law3300) (by native_decide) v.1 v.2
    ((@Law3300.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3349 takes them (1261 nodes). -/
def ordSR4_Law3349 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3349. -/
theorem noSR4_Law3349 : ∀ v : Magma.tupR4,
    ¬ @Equation3349 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3349) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 3)
    (ord := ordSR4_Law3349) (by native_decide) v.1 v.2
    ((@Law3349.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srchR4_refutes_11 :
    FamilyRefutes Magma.srchR4 [
      3296, 3300, 3349
    ] :=
  ⟨noSR4_Law3296, noSR4_Law3300, noSR4_Law3349⟩
