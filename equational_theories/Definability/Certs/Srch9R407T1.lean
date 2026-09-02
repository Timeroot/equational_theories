import equational_theories.Definability.Srch_S9R407

/-!
# Structural certificate targets: `Magma.srch9R407` (part 2 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R407_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `20` equations here, 2,886 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R407_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2051 takes them (262 nodes). -/
def ordS9R407_Law2051 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2051. -/
theorem noS9R407_Law2051 : ∀ v : Magma.tup9R407,
    ¬ @Equation2051 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (286 nodes). -/
def ordS9R407_Law2090 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2090. -/
theorem noS9R407_Law2090 : ∀ v : Magma.tup9R407,
    ¬ @Equation2090 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2306 takes them (81 nodes). -/
def ordS9R407_Law2306 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2306. -/
theorem noS9R407_Law2306 : ∀ v : Magma.tup9R407,
    ¬ @Equation2306 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2306) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law2306) (by native_decide) v.1 v.2
    ((@Law2306.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2322 takes them (81 nodes). -/
def ordS9R407_Law2322 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2322. -/
theorem noS9R407_Law2322 : ∀ v : Magma.tup9R407,
    ¬ @Equation2322 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2322) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 4)
    (ord := ordS9R407_Law2322) (by native_decide) v.1 v.2
    ((@Law2322.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2333 takes them (160 nodes). -/
def ordS9R407_Law2333 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2333. -/
theorem noS9R407_Law2333 : ∀ v : Magma.tup9R407,
    ¬ @Equation2333 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2333) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law2333) (by native_decide) v.1 v.2
    ((@Law2333.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2376 takes them (84 nodes). -/
def ordS9R407_Law2376 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2376. -/
theorem noS9R407_Law2376 : ∀ v : Magma.tup9R407,
    ¬ @Equation2376 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2376) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 4)
    (ord := ordS9R407_Law2376) (by native_decide) v.1 v.2
    ((@Law2376.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2592 takes them (85 nodes). -/
def ordS9R407_Law2592 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2592. -/
theorem noS9R407_Law2592 : ∀ v : Magma.tup9R407,
    ¬ @Equation2592 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2592) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law2592) (by native_decide) v.1 v.2
    ((@Law2592.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2699 takes them (159 nodes). -/
def ordS9R407_Law2699 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2699. -/
theorem noS9R407_Law2699 : ∀ v : Magma.tup9R407,
    ¬ @Equation2699 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2699) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law2699) (by native_decide) v.1 v.2
    ((@Law2699.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2702 takes them (98 nodes). -/
def ordS9R407_Law2702 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2702. -/
theorem noS9R407_Law2702 : ∀ v : Magma.tup9R407,
    ¬ @Equation2702 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2702) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law2702) (by native_decide) v.1 v.2
    ((@Law2702.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2774 takes them (82 nodes). -/
def ordS9R407_Law2774 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2774. -/
theorem noS9R407_Law2774 : ∀ v : Magma.tup9R407,
    ¬ @Equation2774 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2774) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law2774) (by native_decide) v.1 v.2
    ((@Law2774.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2778 takes them (148 nodes). -/
def ordS9R407_Law2778 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2778. -/
theorem noS9R407_Law2778 : ∀ v : Magma.tup9R407,
    ¬ @Equation2778 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2778) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law2778) (by native_decide) v.1 v.2
    ((@Law2778.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2782 takes them (82 nodes). -/
def ordS9R407_Law2782 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2782. -/
theorem noS9R407_Law2782 : ∀ v : Magma.tup9R407,
    ¬ @Equation2782 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2782) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 4)
    (ord := ordS9R407_Law2782) (by native_decide) v.1 v.2
    ((@Law2782.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2808 takes them (21 nodes). -/
def ordS9R407_Law2808 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2808. -/
theorem noS9R407_Law2808 : ∀ v : Magma.tup9R407,
    ¬ @Equation2808 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2808) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law2808) (by native_decide) v.1 v.2
    ((@Law2808.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2998 takes them (117 nodes). -/
def ordS9R407_Law2998 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2998. -/
theorem noS9R407_Law2998 : ∀ v : Magma.tup9R407,
    ¬ @Equation2998 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2998) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law2998) (by native_decide) v.1 v.2
    ((@Law2998.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3201 takes them (117 nodes). -/
def ordS9R407_Law3201 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3201. -/
theorem noS9R407_Law3201 : ∀ v : Magma.tup9R407,
    ¬ @Equation3201 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3201) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3201) (by native_decide) v.1 v.2
    ((@Law3201.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3321 takes them (163 nodes). -/
def ordS9R407_Law3321 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3321. -/
theorem noS9R407_Law3321 : ∀ v : Magma.tup9R407,
    ¬ @Equation3321 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3321) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3321) (by native_decide) v.1 v.2
    ((@Law3321.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (242 nodes). -/
def ordS9R407_Law3343 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3343. -/
theorem noS9R407_Law3343 : ∀ v : Magma.tup9R407,
    ¬ @Equation3343 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (256 nodes). -/
def ordS9R407_Law3414 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3414. -/
theorem noS9R407_Law3414 : ∀ v : Magma.tup9R407,
    ¬ @Equation3414 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3463 takes them (100 nodes). -/
def ordS9R407_Law3463 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3463. -/
theorem noS9R407_Law3463 : ∀ v : Magma.tup9R407,
    ¬ @Equation3463 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3463) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 3)
    (ord := ordS9R407_Law3463) (by native_decide) v.1 v.2
    ((@Law3463.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (262 nodes). -/
def ordS9R407_Law3511 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3511. -/
theorem noS9R407_Law3511 : ∀ v : Magma.tup9R407,
    ¬ @Equation3511 (Fin 9) (Magma.srch9R407 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S9R407.E) (tr := S9R407.tr) (z := S9R407.z)
    (st := S9R407.st) (X := S9R407.X) (envs := Magma.envsRed 9 S9R407.E 2)
    (ord := ordS9R407_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 9) (Magma.srch9R407 v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch9R407_refutes_1 :
    FamilyRefutes Magma.srch9R407 [
      2051, 2090, 2306, 2322, 2333, 2376, 2592, 2699, 2702, 2774, 2778, 2782, 2808, 2998, 3201,
      3321, 3343, 3414, 3463, 3511
    ] :=
  ⟨noS9R407_Law2051, noS9R407_Law2090, noS9R407_Law2306, noS9R407_Law2322, noS9R407_Law2333, noS9R407_Law2376, noS9R407_Law2592, noS9R407_Law2699, noS9R407_Law2702, noS9R407_Law2774, noS9R407_Law2778, noS9R407_Law2782, noS9R407_Law2808, noS9R407_Law2998, noS9R407_Law3201, noS9R407_Law3321, noS9R407_Law3343, noS9R407_Law3414, noS9R407_Law3463, noS9R407_Law3511⟩
