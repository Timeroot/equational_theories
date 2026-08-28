import equational_theories.Definability.Srch_SR101

/-!
# Structural certificate targets: `Magma.srchR101`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR101_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 402 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR101_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3308 takes them (201 nodes). -/
def ordSR101_Law3308 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3308. -/
theorem noSR101_Law3308 : ∀ v : Magma.tupR101,
    ¬ @Equation3308 (Fin 6) (Magma.srchR101 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := SR101.E) (tr := SR101.tr) (z := SR101.z)
    (st := SR101.st) (X := SR101.X) (envs := Magma.envsRed 6 SR101.E 2)
    (ord := ordSR101_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 6) (Magma.srchR101 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (201 nodes). -/
def ordSR101_Law4158 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4158. -/
theorem noSR101_Law4158 : ∀ v : Magma.tupR101,
    ¬ @Equation4158 (Fin 6) (Magma.srchR101 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := SR101.E) (tr := SR101.tr) (z := SR101.z)
    (st := SR101.st) (X := SR101.X) (envs := Magma.envsRed 6 SR101.E 2)
    (ord := ordSR101_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 6) (Magma.srchR101 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR101_refutes_0 :
    FamilyRefutes Magma.srchR101 [
      3308, 4158
    ] :=
  ⟨noSR101_Law3308, noSR101_Law4158⟩
