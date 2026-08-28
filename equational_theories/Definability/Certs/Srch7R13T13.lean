import equational_theories.Definability.Srch_S7R13

/-!
# Structural certificate targets: `Magma.srch7R13` (part 14 of 17)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,509 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3462 takes them (701 nodes). -/
def ordS7R13_Law3462 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3462. -/
theorem noS7R13_Law3462 : ∀ v : Magma.tup7R13,
    ¬ @Equation3462 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3462) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law3462) (by native_decide) v.1 v.2
    ((@Law3462.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3484 takes them (337 nodes). -/
def ordS7R13_Law3484 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3484. -/
theorem noS7R13_Law3484 : ∀ v : Magma.tup7R13,
    ¬ @Equation3484 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3484) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law3484) (by native_decide) v.1 v.2
    ((@Law3484.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3668 takes them (337 nodes). -/
def ordS7R13_Law3668 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3668. -/
theorem noS7R13_Law3668 : ∀ v : Magma.tup7R13,
    ¬ @Equation3668 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3668) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law3668) (by native_decide) v.1 v.2
    ((@Law3668.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3687 takes them (337 nodes). -/
def ordS7R13_Law3687 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3687. -/
theorem noS7R13_Law3687 : ∀ v : Magma.tup7R13,
    ¬ @Equation3687 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3687) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law3687) (by native_decide) v.1 v.2
    ((@Law3687.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3871 takes them (337 nodes). -/
def ordS7R13_Law3871 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3871. -/
theorem noS7R13_Law3871 : ∀ v : Magma.tup7R13,
    ¬ @Equation3871 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3871) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law3871) (by native_decide) v.1 v.2
    ((@Law3871.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3880 takes them (701 nodes). -/
def ordS7R13_Law3880 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3880. -/
theorem noS7R13_Law3880 : ∀ v : Magma.tup7R13,
    ¬ @Equation3880 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3880) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law3880) (by native_decide) v.1 v.2
    ((@Law3880.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4068 takes them (759 nodes). -/
def ordS7R13_Law4068 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4068. -/
theorem noS7R13_Law4068 : ∀ v : Magma.tup7R13,
    ¬ @Equation4068 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4068) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law4068) (by native_decide) v.1 v.2
    ((@Law4068.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch7R13_refutes_13 :
    FamilyRefutes Magma.srch7R13 [
      3462, 3484, 3668, 3687, 3871, 3880, 4068
    ] :=
  ⟨noS7R13_Law3462, noS7R13_Law3484, noS7R13_Law3668, noS7R13_Law3687, noS7R13_Law3871, noS7R13_Law3880, noS7R13_Law4068⟩
