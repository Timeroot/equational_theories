import equational_theories.Definability.Srch_S8R2

/-!
# Structural certificate targets: `Magma.srch8R2` (part 237 of 260)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R2_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 3,105 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R2_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4122 takes them (539 nodes). -/
def ordS8R2_Law4122 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 4122. -/
theorem noS8R2_Law4122 : ∀ v : Magma.tup8R2,
    ¬ @Equation4122 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4122) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law4122) (by native_decide) v.1 v.2
    ((@Law4122.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4123 takes them (491 nodes). -/
def ordS8R2_Law4123 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 4123. -/
theorem noS8R2_Law4123 : ∀ v : Magma.tup8R2,
    ¬ @Equation4123 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4123) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law4123) (by native_decide) v.1 v.2
    ((@Law4123.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4125 takes them (455 nodes). -/
def ordS8R2_Law4125 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 4125. -/
theorem noS8R2_Law4125 : ∀ v : Magma.tup8R2,
    ¬ @Equation4125 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4125) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law4125) (by native_decide) v.1 v.2
    ((@Law4125.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4126 takes them (455 nodes). -/
def ordS8R2_Law4126 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 4126. -/
theorem noS8R2_Law4126 : ∀ v : Magma.tup8R2,
    ¬ @Equation4126 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4126) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law4126) (by native_decide) v.1 v.2
    ((@Law4126.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4137 takes them (597 nodes). -/
def ordS8R2_Law4137 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 4137. -/
theorem noS8R2_Law4137 : ∀ v : Magma.tup8R2,
    ¬ @Equation4137 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4137) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law4137) (by native_decide) v.1 v.2
    ((@Law4137.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4139 takes them (303 nodes). -/
def ordS8R2_Law4139 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 4139. -/
theorem noS8R2_Law4139 : ∀ v : Magma.tup8R2,
    ¬ @Equation4139 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4139) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law4139) (by native_decide) v.1 v.2
    ((@Law4139.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4140 takes them (265 nodes). -/
def ordS8R2_Law4140 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 4140. -/
theorem noS8R2_Law4140 : ∀ v : Magma.tup8R2,
    ¬ @Equation4140 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4140) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law4140) (by native_decide) v.1 v.2
    ((@Law4140.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch8R2_refutes_236 :
    FamilyRefutes Magma.srch8R2 [
      4122, 4123, 4125, 4126, 4137, 4139, 4140
    ] :=
  ⟨noS8R2_Law4122, noS8R2_Law4123, noS8R2_Law4125, noS8R2_Law4126, noS8R2_Law4137, noS8R2_Law4139, noS8R2_Law4140⟩
