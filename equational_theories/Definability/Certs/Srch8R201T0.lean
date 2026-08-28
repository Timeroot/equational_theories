import equational_theories.Definability.Srch_S8R201

/-!
# Structural certificate targets: `Magma.srch8R201`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R201_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `32` equations here, 313 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R201_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 102 takes them (9 nodes). -/
def ordS8R201_Law102 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 102. -/
theorem noS8R201_Law102 : ∀ v : Magma.tup8R201,
    ¬ @Equation102 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law102) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law102) (by native_decide) v.1 v.2
    ((@Law102.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 228 takes them (8 nodes). -/
def ordS8R201_Law228 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 228. -/
theorem noS8R201_Law228 : ∀ v : Magma.tup8R201,
    ¬ @Equation228 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law228) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law228) (by native_decide) v.1 v.2
    ((@Law228.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 417 takes them (9 nodes). -/
def ordS8R201_Law417 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 417. -/
theorem noS8R201_Law417 : ∀ v : Magma.tup8R201,
    ¬ @Equation417 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law417) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law417) (by native_decide) v.1 v.2
    ((@Law417.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 617 takes them (9 nodes). -/
def ordS8R201_Law617 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 617. -/
theorem noS8R201_Law617 : ∀ v : Magma.tup8R201,
    ¬ @Equation617 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law617) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law617) (by native_decide) v.1 v.2
    ((@Law617.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 620 takes them (9 nodes). -/
def ordS8R201_Law620 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 620. -/
theorem noS8R201_Law620 : ∀ v : Magma.tup8R201,
    ¬ @Equation620 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law620) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law620) (by native_decide) v.1 v.2
    ((@Law620.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 826 takes them (9 nodes). -/
def ordS8R201_Law826 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 826. -/
theorem noS8R201_Law826 : ∀ v : Magma.tup8R201,
    ¬ @Equation826 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law826) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law826) (by native_decide) v.1 v.2
    ((@Law826.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1029 takes them (9 nodes). -/
def ordS8R201_Law1029 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1029. -/
theorem noS8R201_Law1029 : ∀ v : Magma.tup8R201,
    ¬ @Equation1029 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1029) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1029) (by native_decide) v.1 v.2
    ((@Law1029.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1226 takes them (11 nodes). -/
def ordS8R201_Law1226 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1226. -/
theorem noS8R201_Law1226 : ∀ v : Magma.tup8R201,
    ¬ @Equation1226 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1226) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1226) (by native_decide) v.1 v.2
    ((@Law1226.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (9 nodes). -/
def ordS8R201_Law1442 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1442. -/
theorem noS8R201_Law1442 : ∀ v : Magma.tup8R201,
    ¬ @Equation1442 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1632 takes them (11 nodes). -/
def ordS8R201_Law1632 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1632. -/
theorem noS8R201_Law1632 : ∀ v : Magma.tup8R201,
    ¬ @Equation1632 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1632) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1632) (by native_decide) v.1 v.2
    ((@Law1632.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1635 takes them (10 nodes). -/
def ordS8R201_Law1635 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1635. -/
theorem noS8R201_Law1635 : ∀ v : Magma.tup8R201,
    ¬ @Equation1635 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1635) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1635) (by native_decide) v.1 v.2
    ((@Law1635.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (9 nodes). -/
def ordS8R201_Law1684 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1684. -/
theorem noS8R201_Law1684 : ∀ v : Magma.tup8R201,
    ¬ @Equation1684 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1691 takes them (8 nodes). -/
def ordS8R201_Law1691 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1691. -/
theorem noS8R201_Law1691 : ∀ v : Magma.tup8R201,
    ¬ @Equation1691 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1691) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1691) (by native_decide) v.1 v.2
    ((@Law1691.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1838 takes them (9 nodes). -/
def ordS8R201_Law1838 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1838. -/
theorem noS8R201_Law1838 : ∀ v : Magma.tup8R201,
    ¬ @Equation1838 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1838) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1838) (by native_decide) v.1 v.2
    ((@Law1838.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (9 nodes). -/
def ordS8R201_Law1848 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1848. -/
theorem noS8R201_Law1848 : ∀ v : Magma.tup8R201,
    ¬ @Equation1848 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1894 takes them (10 nodes). -/
def ordS8R201_Law1894 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1894. -/
theorem noS8R201_Law1894 : ∀ v : Magma.tup8R201,
    ¬ @Equation1894 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1894) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1894) (by native_decide) v.1 v.2
    ((@Law1894.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1921 takes them (11 nodes). -/
def ordS8R201_Law1921 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1921. -/
theorem noS8R201_Law1921 : ∀ v : Magma.tup8R201,
    ¬ @Equation1921 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1921) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law1921) (by native_decide) v.1 v.2
    ((@Law1921.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (8 nodes). -/
def ordS8R201_Law2090 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2090. -/
theorem noS8R201_Law2090 : ∀ v : Magma.tup8R201,
    ¬ @Equation2090 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2327 takes them (11 nodes). -/
def ordS8R201_Law2327 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2327. -/
theorem noS8R201_Law2327 : ∀ v : Magma.tup8R201,
    ¬ @Equation2327 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2327) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law2327) (by native_decide) v.1 v.2
    ((@Law2327.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2540 takes them (8 nodes). -/
def ordS8R201_Law2540 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2540. -/
theorem noS8R201_Law2540 : ∀ v : Magma.tup8R201,
    ¬ @Equation2540 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2540) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law2540) (by native_decide) v.1 v.2
    ((@Law2540.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2743 takes them (8 nodes). -/
def ordS8R201_Law2743 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2743. -/
theorem noS8R201_Law2743 : ∀ v : Magma.tup8R201,
    ¬ @Equation2743 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2743) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law2743) (by native_decide) v.1 v.2
    ((@Law2743.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2909 takes them (9 nodes). -/
def ordS8R201_Law2909 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2909. -/
theorem noS8R201_Law2909 : ∀ v : Magma.tup8R201,
    ¬ @Equation2909 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2936 takes them (8 nodes). -/
def ordS8R201_Law2936 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2936. -/
theorem noS8R201_Law2936 : ∀ v : Magma.tup8R201,
    ¬ @Equation2936 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2936) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law2936) (by native_decide) v.1 v.2
    ((@Law2936.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (8 nodes). -/
def ordS8R201_Law3112 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3112. -/
theorem noS8R201_Law3112 : ∀ v : Magma.tup8R201,
    ¬ @Equation3112 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3259 takes them (11 nodes). -/
def ordS8R201_Law3259 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3259. -/
theorem noS8R201_Law3259 : ∀ v : Magma.tup8R201,
    ¬ @Equation3259 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3259) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law3259) (by native_decide) v.1 v.2
    ((@Law3259.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (15 nodes). -/
def ordS8R201_Law3334 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3334. -/
theorem noS8R201_Law3334 : ∀ v : Magma.tup8R201,
    ¬ @Equation3334 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 3)
    (ord := ordS8R201_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3459 takes them (11 nodes). -/
def ordS8R201_Law3459 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3459. -/
theorem noS8R201_Law3459 : ∀ v : Magma.tup8R201,
    ¬ @Equation3459 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3459) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law3459) (by native_decide) v.1 v.2
    ((@Law3459.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3462 takes them (10 nodes). -/
def ordS8R201_Law3462 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3462. -/
theorem noS8R201_Law3462 : ∀ v : Magma.tup8R201,
    ¬ @Equation3462 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3462) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law3462) (by native_decide) v.1 v.2
    ((@Law3462.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3880 takes them (10 nodes). -/
def ordS8R201_Law3880 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3880. -/
theorem noS8R201_Law3880 : ∀ v : Magma.tup8R201,
    ¬ @Equation3880 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3880) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law3880) (by native_decide) v.1 v.2
    ((@Law3880.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3887 takes them (11 nodes). -/
def ordS8R201_Law3887 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3887. -/
theorem noS8R201_Law3887 : ∀ v : Magma.tup8R201,
    ¬ @Equation3887 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3887) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law3887) (by native_decide) v.1 v.2
    ((@Law3887.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4083 takes them (11 nodes). -/
def ordS8R201_Law4083 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4083. -/
theorem noS8R201_Law4083 : ∀ v : Magma.tup8R201,
    ¬ @Equation4083 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4083) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 2)
    (ord := ordS8R201_Law4083) (by native_decide) v.1 v.2
    ((@Law4083.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (15 nodes). -/
def ordS8R201_Law4146 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4146. -/
theorem noS8R201_Law4146 : ∀ v : Magma.tup8R201,
    ¬ @Equation4146 (Fin 8) (Magma.srch8R201 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S8R201.E) (tr := S8R201.tr) (z := S8R201.z)
    (st := S8R201.st) (X := S8R201.X) (envs := Magma.envsRed 8 S8R201.E 3)
    (ord := ordS8R201_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 8) (Magma.srch8R201 v)).mpr hv)

/-- No member of the class satisfies any of these `32` equations. -/
theorem srch8R201_refutes_0 :
    FamilyRefutes Magma.srch8R201 [
      102, 228, 417, 617, 620, 826, 1029, 1226, 1442, 1632, 1635, 1684, 1691, 1838, 1848, 1894,
      1921, 2090, 2327, 2540, 2743, 2909, 2936, 3112, 3259, 3334, 3459, 3462, 3880, 3887, 4083,
      4146
    ] :=
  ⟨noS8R201_Law102, noS8R201_Law228, noS8R201_Law417, noS8R201_Law617, noS8R201_Law620, noS8R201_Law826, noS8R201_Law1029, noS8R201_Law1226, noS8R201_Law1442, noS8R201_Law1632, noS8R201_Law1635, noS8R201_Law1684, noS8R201_Law1691, noS8R201_Law1838, noS8R201_Law1848, noS8R201_Law1894, noS8R201_Law1921, noS8R201_Law2090, noS8R201_Law2327, noS8R201_Law2540, noS8R201_Law2743, noS8R201_Law2909, noS8R201_Law2936, noS8R201_Law3112, noS8R201_Law3259, noS8R201_Law3334, noS8R201_Law3459, noS8R201_Law3462, noS8R201_Law3880, noS8R201_Law3887, noS8R201_Law4083, noS8R201_Law4146⟩
