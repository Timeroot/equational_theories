import equational_theories.Definability.Srch_SR4

/-!
# Structural certificate targets: `Magma.srchR4` (part 35 of 37)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR4_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 3,033 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR4_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4148 takes them (2192 nodes). -/
def ordSR4_Law4148 : List (Fin 12) := [0, 4, 11, 9, 7, 2, 8, 6, 10, 5, 3, 1]

/-- No member of the class satisfies equation 4148. -/
theorem noSR4_Law4148 : ∀ v : Magma.tupR4,
    ¬ @Equation4148 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4148) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4148) (by native_decide) v.1 v.2
    ((@Law4148.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4149 takes them (431 nodes). -/
def ordSR4_Law4149 : List (Fin 12) := [8, 9, 4, 10, 11, 1, 0, 5, 7, 6, 2, 3]

/-- No member of the class satisfies equation 4149. -/
theorem noSR4_Law4149 : ∀ v : Magma.tupR4,
    ¬ @Equation4149 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4149) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4149) (by native_decide) v.1 v.2
    ((@Law4149.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4151 takes them (410 nodes). -/
def ordSR4_Law4151 : List (Fin 12) := [10, 11, 0, 3, 7, 6, 4, 1, 2, 9, 5, 8]

/-- No member of the class satisfies equation 4151. -/
theorem noSR4_Law4151 : ∀ v : Magma.tupR4,
    ¬ @Equation4151 (Fin 6) (Magma.srchR4 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4151) (E := SR4.E) (tr := SR4.tr) (z := SR4.z)
    (st := SR4.st) (X := SR4.X) (envs := Magma.envsRed 6 SR4.E 4)
    (ord := ordSR4_Law4151) (by native_decide) v.1 v.2
    ((@Law4151.models_iff (Fin 6) (Magma.srchR4 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srchR4_refutes_34 :
    FamilyRefutes Magma.srchR4 [
      4148, 4149, 4151
    ] :=
  ⟨noSR4_Law4148, noSR4_Law4149, noSR4_Law4151⟩
