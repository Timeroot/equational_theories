import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 59 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 768 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4675 takes them (152 nodes). -/
def ordS7R12_Law4675 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4675. -/
theorem noS7R12_Law4675 : ∀ v : Magma.tup7R12,
    ¬ @Equation4675 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4675) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4675) (by native_decide) v.1 v.2
    ((@Law4675.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4676 takes them (22 nodes). -/
def ordS7R12_Law4676 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4676. -/
theorem noS7R12_Law4676 : ∀ v : Magma.tup7R12,
    ¬ @Equation4676 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4676) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 5)
    (ord := ordS7R12_Law4676) (by native_decide) v.1 v.2
    ((@Law4676.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4677 takes them (412 nodes). -/
def ordS7R12_Law4677 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4677. -/
theorem noS7R12_Law4677 : ∀ v : Magma.tup7R12,
    ¬ @Equation4677 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4677) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4677) (by native_decide) v.1 v.2
    ((@Law4677.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4682 takes them (48 nodes). -/
def ordS7R12_Law4682 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4682. -/
theorem noS7R12_Law4682 : ∀ v : Magma.tup7R12,
    ¬ @Equation4682 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4682) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4682) (by native_decide) v.1 v.2
    ((@Law4682.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4689 takes them (112 nodes). -/
def ordS7R12_Law4689 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4689. -/
theorem noS7R12_Law4689 : ∀ v : Magma.tup7R12,
    ¬ @Equation4689 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4689) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4689) (by native_decide) v.1 v.2
    ((@Law4689.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4693 takes them (22 nodes). -/
def ordS7R12_Law4693 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4693. -/
theorem noS7R12_Law4693 : ∀ v : Magma.tup7R12,
    ¬ @Equation4693 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4693) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 5)
    (ord := ordS7R12_Law4693) (by native_decide) v.1 v.2
    ((@Law4693.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch7R12_refutes_58 :
    FamilyRefutes Magma.srch7R12 [
      4675, 4676, 4677, 4682, 4689, 4693
    ] :=
  ⟨noS7R12_Law4675, noS7R12_Law4676, noS7R12_Law4677, noS7R12_Law4682, noS7R12_Law4689, noS7R12_Law4693⟩
