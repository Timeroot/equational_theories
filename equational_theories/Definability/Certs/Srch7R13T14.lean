import equational_theories.Definability.Srch_S7R13

/-!
# Structural certificate targets: `Magma.srch7R13` (part 15 of 17)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 3,656 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4135 takes them (735 nodes). -/
def ordS7R13_Law4135 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4135. -/
theorem noS7R13_Law4135 : ∀ v : Magma.tup7R13,
    ¬ @Equation4135 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (953 nodes). -/
def ordS7R13_Law4146 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4146. -/
theorem noS7R13_Law4146 : ∀ v : Magma.tup7R13,
    ¬ @Equation4146 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4175 takes them (189 nodes). -/
def ordS7R13_Law4175 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4175. -/
theorem noS7R13_Law4175 : ∀ v : Magma.tup7R13,
    ¬ @Equation4175 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4175) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law4175) (by native_decide) v.1 v.2
    ((@Law4175.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4226 takes them (193 nodes). -/
def ordS7R13_Law4226 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4226. -/
theorem noS7R13_Law4226 : ∀ v : Magma.tup7R13,
    ¬ @Equation4226 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4226) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law4226) (by native_decide) v.1 v.2
    ((@Law4226.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4243 takes them (189 nodes). -/
def ordS7R13_Law4243 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4243. -/
theorem noS7R13_Law4243 : ∀ v : Magma.tup7R13,
    ¬ @Equation4243 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4243) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 4)
    (ord := ordS7R13_Law4243) (by native_decide) v.1 v.2
    ((@Law4243.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4275 takes them (1397 nodes). -/
def ordS7R13_Law4275 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4275. -/
theorem noS7R13_Law4275 : ∀ v : Magma.tup7R13,
    ¬ @Equation4275 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch7R13_refutes_14 :
    FamilyRefutes Magma.srch7R13 [
      4135, 4146, 4175, 4226, 4243, 4275
    ] :=
  ⟨noS7R13_Law4135, noS7R13_Law4146, noS7R13_Law4175, noS7R13_Law4226, noS7R13_Law4243, noS7R13_Law4275⟩
