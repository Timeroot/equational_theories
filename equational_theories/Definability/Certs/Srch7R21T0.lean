import equational_theories.Definability.Srch_S7R21

/-!
# Structural certificate targets: `Magma.srch7R21`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R21_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `22` equations here, 2,156 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R21_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 679 takes them (172 nodes). -/
def ordS7R21_Law679 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 679. -/
theorem noS7R21_Law679 : ∀ v : Magma.tup7R21,
    ¬ @Equation679 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law679) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law679) (by native_decide) v.1 v.2
    ((@Law679.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 716 takes them (82 nodes). -/
def ordS7R21_Law716 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 716. -/
theorem noS7R21_Law716 : ∀ v : Magma.tup7R21,
    ¬ @Equation716 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law716) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law716) (by native_decide) v.1 v.2
    ((@Law716.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 879 takes them (141 nodes). -/
def ordS7R21_Law879 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 879. -/
theorem noS7R21_Law879 : ∀ v : Magma.tup7R21,
    ¬ @Equation879 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law879) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law879) (by native_decide) v.1 v.2
    ((@Law879.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 919 takes them (82 nodes). -/
def ordS7R21_Law919 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 919. -/
theorem noS7R21_Law919 : ∀ v : Magma.tup7R21,
    ¬ @Equation919 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law919) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law919) (by native_decide) v.1 v.2
    ((@Law919.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1518 takes them (172 nodes). -/
def ordS7R21_Law1518 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1518. -/
theorem noS7R21_Law1518 : ∀ v : Magma.tup7R21,
    ¬ @Equation1518 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1518) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law1518) (by native_decide) v.1 v.2
    ((@Law1518.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1528 takes them (82 nodes). -/
def ordS7R21_Law1528 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1528. -/
theorem noS7R21_Law1528 : ∀ v : Magma.tup7R21,
    ¬ @Equation1528 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1528) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law1528) (by native_decide) v.1 v.2
    ((@Law1528.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2054 takes them (172 nodes). -/
def ordS7R21_Law2054 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2054. -/
theorem noS7R21_Law2054 : ∀ v : Magma.tup7R21,
    ¬ @Equation2054 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2054) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law2054) (by native_decide) v.1 v.2
    ((@Law2054.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2064 takes them (100 nodes). -/
def ordS7R21_Law2064 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2064. -/
theorem noS7R21_Law2064 : ∀ v : Magma.tup7R21,
    ¬ @Equation2064 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2064) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law2064) (by native_decide) v.1 v.2
    ((@Law2064.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2650 takes them (141 nodes). -/
def ordS7R21_Law2650 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2650. -/
theorem noS7R21_Law2650 : ∀ v : Magma.tup7R21,
    ¬ @Equation2650 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2650) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law2650) (by native_decide) v.1 v.2
    ((@Law2650.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2673 takes them (100 nodes). -/
def ordS7R21_Law2673 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2673. -/
theorem noS7R21_Law2673 : ∀ v : Magma.tup7R21,
    ¬ @Equation2673 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2673) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law2673) (by native_decide) v.1 v.2
    ((@Law2673.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2873 takes them (172 nodes). -/
def ordS7R21_Law2873 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2873. -/
theorem noS7R21_Law2873 : ∀ v : Magma.tup7R21,
    ¬ @Equation2873 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2873) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law2873) (by native_decide) v.1 v.2
    ((@Law2873.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2876 takes them (100 nodes). -/
def ordS7R21_Law2876 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2876. -/
theorem noS7R21_Law2876 : ∀ v : Magma.tup7R21,
    ¬ @Equation2876 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2876) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 2)
    (ord := ordS7R21_Law2876) (by native_decide) v.1 v.2
    ((@Law2876.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3520 takes them (60 nodes). -/
def ordS7R21_Law3520 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3520. -/
theorem noS7R21_Law3520 : ∀ v : Magma.tup7R21,
    ¬ @Equation3520 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3520) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 3)
    (ord := ordS7R21_Law3520) (by native_decide) v.1 v.2
    ((@Law3520.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3523 takes them (58 nodes). -/
def ordS7R21_Law3523 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3523. -/
theorem noS7R21_Law3523 : ∀ v : Magma.tup7R21,
    ¬ @Equation3523 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3523) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 3)
    (ord := ordS7R21_Law3523) (by native_decide) v.1 v.2
    ((@Law3523.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3524 takes them (71 nodes). -/
def ordS7R21_Law3524 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3524. -/
theorem noS7R21_Law3524 : ∀ v : Magma.tup7R21,
    ¬ @Equation3524 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3524) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 3)
    (ord := ordS7R21_Law3524) (by native_decide) v.1 v.2
    ((@Law3524.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3527 takes them (58 nodes). -/
def ordS7R21_Law3527 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3527. -/
theorem noS7R21_Law3527 : ∀ v : Magma.tup7R21,
    ¬ @Equation3527 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3527) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 4)
    (ord := ordS7R21_Law3527) (by native_decide) v.1 v.2
    ((@Law3527.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3529 takes them (58 nodes). -/
def ordS7R21_Law3529 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3529. -/
theorem noS7R21_Law3529 : ∀ v : Magma.tup7R21,
    ¬ @Equation3529 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3529) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 3)
    (ord := ordS7R21_Law3529) (by native_decide) v.1 v.2
    ((@Law3529.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3931 takes them (76 nodes). -/
def ordS7R21_Law3931 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3931. -/
theorem noS7R21_Law3931 : ∀ v : Magma.tup7R21,
    ¬ @Equation3931 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3931) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 3)
    (ord := ordS7R21_Law3931) (by native_decide) v.1 v.2
    ((@Law3931.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3972 takes them (71 nodes). -/
def ordS7R21_Law3972 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3972. -/
theorem noS7R21_Law3972 : ∀ v : Magma.tup7R21,
    ¬ @Equation3972 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3972) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 3)
    (ord := ordS7R21_Law3972) (by native_decide) v.1 v.2
    ((@Law3972.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3989 takes them (58 nodes). -/
def ordS7R21_Law3989 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3989. -/
theorem noS7R21_Law3989 : ∀ v : Magma.tup7R21,
    ¬ @Equation3989 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3989) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 3)
    (ord := ordS7R21_Law3989) (by native_decide) v.1 v.2
    ((@Law3989.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4006 takes them (72 nodes). -/
def ordS7R21_Law4006 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4006. -/
theorem noS7R21_Law4006 : ∀ v : Magma.tup7R21,
    ¬ @Equation4006 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4006) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 3)
    (ord := ordS7R21_Law4006) (by native_decide) v.1 v.2
    ((@Law4006.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4040 takes them (58 nodes). -/
def ordS7R21_Law4040 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4040. -/
theorem noS7R21_Law4040 : ∀ v : Magma.tup7R21,
    ¬ @Equation4040 (Fin 7) (Magma.srch7R21 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4040) (E := S7R21.E) (tr := S7R21.tr) (z := S7R21.z)
    (st := S7R21.st) (X := S7R21.X) (envs := Magma.envsRed 7 S7R21.E 4)
    (ord := ordS7R21_Law4040) (by native_decide) v.1 v.2
    ((@Law4040.models_iff (Fin 7) (Magma.srch7R21 v)).mpr hv)

/-- No member of the class satisfies any of these `22` equations. -/
theorem srch7R21_refutes_0 :
    FamilyRefutes Magma.srch7R21 [
      679, 716, 879, 919, 1518, 1528, 2054, 2064, 2650, 2673, 2873, 2876, 3520, 3523, 3524, 3527,
      3529, 3931, 3972, 3989, 4006, 4040
    ] :=
  ⟨noS7R21_Law679, noS7R21_Law716, noS7R21_Law879, noS7R21_Law919, noS7R21_Law1518, noS7R21_Law1528, noS7R21_Law2054, noS7R21_Law2064, noS7R21_Law2650, noS7R21_Law2673, noS7R21_Law2873, noS7R21_Law2876, noS7R21_Law3520, noS7R21_Law3523, noS7R21_Law3524, noS7R21_Law3527, noS7R21_Law3529, noS7R21_Law3931, noS7R21_Law3972, noS7R21_Law3989, noS7R21_Law4006, noS7R21_Law4040⟩
