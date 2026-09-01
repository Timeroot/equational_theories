import equational_theories.Definability.Srch_SR16

/-!
# Structural certificate targets: `Magma.srchR16`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR16_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `4`
equations here, 396 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR16_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 960 takes them (54 nodes). -/
def ordSR16_Law960 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 960. -/
theorem noSR16_Law960 : ∀ v : Magma.tupR16,
    ¬ @Equation960 (Fin 6) (Magma.srchR16 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law960) (E := SR16.E) (tr := SR16.tr) (z := SR16.z)
    (st := SR16.st) (X := SR16.X) (envs := Magma.envsRed 6 SR16.E 3)
    (ord := ordSR16_Law960) (by native_decide) v.1 v.2
    ((@Law960.models_iff (Fin 6) (Magma.srchR16 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1560 takes them (144 nodes). -/
def ordSR16_Law1560 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1560. -/
theorem noSR16_Law1560 : ∀ v : Magma.tupR16,
    ¬ @Equation1560 (Fin 6) (Magma.srchR16 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1560) (E := SR16.E) (tr := SR16.tr) (z := SR16.z)
    (st := SR16.st) (X := SR16.X) (envs := Magma.envsRed 6 SR16.E 3)
    (ord := ordSR16_Law1560) (by native_decide) v.1 v.2
    ((@Law1560.models_iff (Fin 6) (Magma.srchR16 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2055 takes them (144 nodes). -/
def ordSR16_Law2055 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2055. -/
theorem noSR16_Law2055 : ∀ v : Magma.tupR16,
    ¬ @Equation2055 (Fin 6) (Magma.srchR16 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2055) (E := SR16.E) (tr := SR16.tr) (z := SR16.z)
    (st := SR16.st) (X := SR16.X) (envs := Magma.envsRed 6 SR16.E 3)
    (ord := ordSR16_Law2055) (by native_decide) v.1 v.2
    ((@Law2055.models_iff (Fin 6) (Magma.srchR16 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2656 takes them (54 nodes). -/
def ordSR16_Law2656 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2656. -/
theorem noSR16_Law2656 : ∀ v : Magma.tupR16,
    ¬ @Equation2656 (Fin 6) (Magma.srchR16 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2656) (E := SR16.E) (tr := SR16.tr) (z := SR16.z)
    (st := SR16.st) (X := SR16.X) (envs := Magma.envsRed 6 SR16.E 3)
    (ord := ordSR16_Law2656) (by native_decide) v.1 v.2
    ((@Law2656.models_iff (Fin 6) (Magma.srchR16 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srchR16_refutes_0 :
    FamilyRefutes Magma.srchR16 [
      960, 1560, 2055, 2656
    ] :=
  ⟨noSR16_Law960, noSR16_Law1560, noSR16_Law2055, noSR16_Law2656⟩
