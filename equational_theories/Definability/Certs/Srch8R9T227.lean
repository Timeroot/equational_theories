import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 228 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 2,687 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4078 takes them (768 nodes). -/
def ordS8R9_Law4078 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4078. -/
theorem noS8R9_Law4078 : ∀ v : Magma.tup8R9,
    ¬ @Equation4078 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4078) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4078) (by native_decide) v.1 v.2
    ((@Law4078.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4079 takes them (49 nodes). -/
def ordS8R9_Law4079 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4079. -/
theorem noS8R9_Law4079 : ∀ v : Magma.tup8R9,
    ¬ @Equation4079 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4079) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4079) (by native_decide) v.1 v.2
    ((@Law4079.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4086 takes them (195 nodes). -/
def ordS8R9_Law4086 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4086. -/
theorem noS8R9_Law4086 : ∀ v : Magma.tup8R9,
    ¬ @Equation4086 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4086) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4086) (by native_decide) v.1 v.2
    ((@Law4086.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4096 takes them (65 nodes). -/
def ordS8R9_Law4096 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4096. -/
theorem noS8R9_Law4096 : ∀ v : Magma.tup8R9,
    ¬ @Equation4096 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4096) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4096) (by native_decide) v.1 v.2
    ((@Law4096.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4104 takes them (776 nodes). -/
def ordS8R9_Law4104 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4104. -/
theorem noS8R9_Law4104 : ∀ v : Magma.tup8R9,
    ¬ @Equation4104 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4104) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4104) (by native_decide) v.1 v.2
    ((@Law4104.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4108 takes them (769 nodes). -/
def ordS8R9_Law4108 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4108. -/
theorem noS8R9_Law4108 : ∀ v : Magma.tup8R9,
    ¬ @Equation4108 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4108) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law4108) (by native_decide) v.1 v.2
    ((@Law4108.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4112 takes them (65 nodes). -/
def ordS8R9_Law4112 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4112. -/
theorem noS8R9_Law4112 : ∀ v : Magma.tup8R9,
    ¬ @Equation4112 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4112) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law4112) (by native_decide) v.1 v.2
    ((@Law4112.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch8R9_refutes_227 :
    FamilyRefutes Magma.srch8R9 [
      4078, 4079, 4086, 4096, 4104, 4108, 4112
    ] :=
  ⟨noS8R9_Law4078, noS8R9_Law4079, noS8R9_Law4086, noS8R9_Law4096, noS8R9_Law4104, noS8R9_Law4108, noS8R9_Law4112⟩
