import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 18 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 3,588 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4040 takes them (417 nodes). -/
def ordS8R52_Law4040 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4040. -/
theorem noS8R52_Law4040 : ∀ v : Magma.tup8R52,
    ¬ @Equation4040 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4040) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law4040) (by native_decide) v.1 v.2
    ((@Law4040.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4068 takes them (513 nodes). -/
def ordS8R52_Law4068 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4068. -/
theorem noS8R52_Law4068 : ∀ v : Magma.tup8R52,
    ¬ @Equation4068 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4068) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4068) (by native_decide) v.1 v.2
    ((@Law4068.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (273 nodes). -/
def ordS8R52_Law4130 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4130. -/
theorem noS8R52_Law4130 : ∀ v : Magma.tup8R52,
    ¬ @Equation4130 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (433 nodes). -/
def ordS8R52_Law4146 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4146. -/
theorem noS8R52_Law4146 : ∀ v : Magma.tup8R52,
    ¬ @Equation4146 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4275 takes them (953 nodes). -/
def ordS8R52_Law4275 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4275. -/
theorem noS8R52_Law4275 : ∀ v : Magma.tup8R52,
    ¬ @Equation4275 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (225 nodes). -/
def ordS8R52_Law4283 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4283. -/
theorem noS8R52_Law4283 : ∀ v : Magma.tup8R52,
    ¬ @Equation4283 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4291 takes them (301 nodes). -/
def ordS8R52_Law4291 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4291. -/
theorem noS8R52_Law4291 : ∀ v : Magma.tup8R52,
    ¬ @Equation4291 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4291) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law4291) (by native_decide) v.1 v.2
    ((@Law4291.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4307 takes them (473 nodes). -/
def ordS8R52_Law4307 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4307. -/
theorem noS8R52_Law4307 : ∀ v : Magma.tup8R52,
    ¬ @Equation4307 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch8R52_refutes_17 :
    FamilyRefutes Magma.srch8R52 [
      4040, 4068, 4130, 4146, 4275, 4283, 4291, 4307
    ] :=
  ⟨noS8R52_Law4040, noS8R52_Law4068, noS8R52_Law4130, noS8R52_Law4146, noS8R52_Law4275, noS8R52_Law4283, noS8R52_Law4291, noS8R52_Law4307⟩
