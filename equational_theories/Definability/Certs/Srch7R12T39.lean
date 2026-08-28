import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 40 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,508 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3758 takes them (1973 nodes). -/
def ordS7R12_Law3758 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3758. -/
theorem noS7R12_Law3758 : ∀ v : Magma.tup7R12,
    ¬ @Equation3758 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3758) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3758) (by native_decide) v.1 v.2
    ((@Law3758.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3761 takes them (661 nodes). -/
def ordS7R12_Law3761 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3761. -/
theorem noS7R12_Law3761 : ∀ v : Magma.tup7R12,
    ¬ @Equation3761 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3761) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3761) (by native_decide) v.1 v.2
    ((@Law3761.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3786 takes them (85 nodes). -/
def ordS7R12_Law3786 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3786. -/
theorem noS7R12_Law3786 : ∀ v : Magma.tup7R12,
    ¬ @Equation3786 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3786) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3786) (by native_decide) v.1 v.2
    ((@Law3786.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3790 takes them (99 nodes). -/
def ordS7R12_Law3790 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3790. -/
theorem noS7R12_Law3790 : ∀ v : Magma.tup7R12,
    ¬ @Equation3790 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3790) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3790) (by native_decide) v.1 v.2
    ((@Law3790.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3803 takes them (75 nodes). -/
def ordS7R12_Law3803 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3803. -/
theorem noS7R12_Law3803 : ∀ v : Magma.tup7R12,
    ¬ @Equation3803 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3803) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3803) (by native_decide) v.1 v.2
    ((@Law3803.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3823 takes them (615 nodes). -/
def ordS7R12_Law3823 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3823. -/
theorem noS7R12_Law3823 : ∀ v : Magma.tup7R12,
    ¬ @Equation3823 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3823) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3823) (by native_decide) v.1 v.2
    ((@Law3823.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch7R12_refutes_39 :
    FamilyRefutes Magma.srch7R12 [
      3758, 3761, 3786, 3790, 3803, 3823
    ] :=
  ⟨noS7R12_Law3758, noS7R12_Law3761, noS7R12_Law3786, noS7R12_Law3790, noS7R12_Law3803, noS7R12_Law3823⟩
