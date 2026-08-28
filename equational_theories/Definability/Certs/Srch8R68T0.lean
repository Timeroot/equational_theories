import equational_theories.Definability.Srch_S8R68

/-!
# Structural certificate targets: `Magma.srch8R68`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R68_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `24` equations here, 619 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R68_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 430 takes them (25 nodes). -/
def ordS8R68_Law430 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 430. -/
theorem noS8R68_Law430 : ∀ v : Magma.tup8R68,
    ¬ @Equation430 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law430) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law430) (by native_decide) v.1 v.2
    ((@Law430.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 442 takes them (21 nodes). -/
def ordS8R68_Law442 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 442. -/
theorem noS8R68_Law442 : ∀ v : Magma.tup8R68,
    ¬ @Equation442 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law442) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law442) (by native_decide) v.1 v.2
    ((@Law442.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 455 takes them (21 nodes). -/
def ordS8R68_Law455 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 455. -/
theorem noS8R68_Law455 : ∀ v : Magma.tup8R68,
    ¬ @Equation455 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law455) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law455) (by native_decide) v.1 v.2
    ((@Law455.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1434 takes them (42 nodes). -/
def ordS8R68_Law1434 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1434. -/
theorem noS8R68_Law1434 : ∀ v : Magma.tup8R68,
    ¬ @Equation1434 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1434) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law1434) (by native_decide) v.1 v.2
    ((@Law1434.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (50 nodes). -/
def ordS8R68_Law1654 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1654. -/
theorem noS8R68_Law1654 : ∀ v : Magma.tup8R68,
    ¬ @Equation1654 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1657 takes them (36 nodes). -/
def ordS8R68_Law1657 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1657. -/
theorem noS8R68_Law1657 : ∀ v : Magma.tup8R68,
    ¬ @Equation1657 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1657) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law1657) (by native_decide) v.1 v.2
    ((@Law1657.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1721 takes them (21 nodes). -/
def ordS8R68_Law1721 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1721. -/
theorem noS8R68_Law1721 : ∀ v : Magma.tup8R68,
    ¬ @Equation1721 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1721) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law1721) (by native_decide) v.1 v.2
    ((@Law1721.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (50 nodes). -/
def ordS8R68_Law1840 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1840. -/
theorem noS8R68_Law1840 : ∀ v : Magma.tup8R68,
    ¬ @Equation1840 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1851 takes them (21 nodes). -/
def ordS8R68_Law1851 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1851. -/
theorem noS8R68_Law1851 : ∀ v : Magma.tup8R68,
    ¬ @Equation1851 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1851) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law1851) (by native_decide) v.1 v.2
    ((@Law1851.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1860 takes them (36 nodes). -/
def ordS8R68_Law1860 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 1860. -/
theorem noS8R68_Law1860 : ∀ v : Magma.tup8R68,
    ¬ @Equation1860 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1860) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law1860) (by native_decide) v.1 v.2
    ((@Law1860.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2060 takes them (42 nodes). -/
def ordS8R68_Law2060 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 2060. -/
theorem noS8R68_Law2060 : ∀ v : Magma.tup8R68,
    ¬ @Equation2060 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2060) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law2060) (by native_decide) v.1 v.2
    ((@Law2060.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3093 takes them (21 nodes). -/
def ordS8R68_Law3093 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3093. -/
theorem noS8R68_Law3093 : ∀ v : Magma.tup8R68,
    ¬ @Equation3093 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3093) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law3093) (by native_decide) v.1 v.2
    ((@Law3093.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (24 nodes). -/
def ordS8R68_Law3142 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3142. -/
theorem noS8R68_Law3142 : ∀ v : Magma.tup8R68,
    ¬ @Equation3142 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 2)
    (ord := ordS8R68_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3214 takes them (20 nodes). -/
def ordS8R68_Law3214 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3214. -/
theorem noS8R68_Law3214 : ∀ v : Magma.tup8R68,
    ¬ @Equation3214 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3214) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law3214) (by native_decide) v.1 v.2
    ((@Law3214.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (28 nodes). -/
def ordS8R68_Law3414 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3414. -/
theorem noS8R68_Law3414 : ∀ v : Magma.tup8R68,
    ¬ @Equation3414 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (28 nodes). -/
def ordS8R68_Law3526 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3526. -/
theorem noS8R68_Law3526 : ∀ v : Magma.tup8R68,
    ¬ @Equation3526 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (28 nodes). -/
def ordS8R68_Law4023 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4023. -/
theorem noS8R68_Law4023 : ∀ v : Magma.tup8R68,
    ¬ @Equation4023 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (28 nodes). -/
def ordS8R68_Law4135 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4135. -/
theorem noS8R68_Law4135 : ∀ v : Magma.tup8R68,
    ¬ @Equation4135 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4315 takes them (15 nodes). -/
def ordS8R68_Law4315 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4315. -/
theorem noS8R68_Law4315 : ∀ v : Magma.tup8R68,
    ¬ @Equation4315 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4315) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law4315) (by native_decide) v.1 v.2
    ((@Law4315.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4339 takes them (11 nodes). -/
def ordS8R68_Law4339 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4339. -/
theorem noS8R68_Law4339 : ∀ v : Magma.tup8R68,
    ¬ @Equation4339 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4339) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law4339) (by native_decide) v.1 v.2
    ((@Law4339.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4357 takes them (11 nodes). -/
def ordS8R68_Law4357 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4357. -/
theorem noS8R68_Law4357 : ∀ v : Magma.tup8R68,
    ¬ @Equation4357 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4357) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 4)
    (ord := ordS8R68_Law4357) (by native_decide) v.1 v.2
    ((@Law4357.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4615 takes them (12 nodes). -/
def ordS8R68_Law4615 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4615. -/
theorem noS8R68_Law4615 : ∀ v : Magma.tup8R68,
    ¬ @Equation4615 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4615) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law4615) (by native_decide) v.1 v.2
    ((@Law4615.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4645 takes them (16 nodes). -/
def ordS8R68_Law4645 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4645. -/
theorem noS8R68_Law4645 : ∀ v : Magma.tup8R68,
    ¬ @Equation4645 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4645) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 3)
    (ord := ordS8R68_Law4645) (by native_decide) v.1 v.2
    ((@Law4645.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4689 takes them (12 nodes). -/
def ordS8R68_Law4689 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 4689. -/
theorem noS8R68_Law4689 : ∀ v : Magma.tup8R68,
    ¬ @Equation4689 (Fin 8) (Magma.srch8R68 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4689) (E := S8R68.E) (tr := S8R68.tr) (z := S8R68.z)
    (st := S8R68.st) (X := S8R68.X) (envs := Magma.envsRed 8 S8R68.E 4)
    (ord := ordS8R68_Law4689) (by native_decide) v.1 v.2
    ((@Law4689.models_iff (Fin 8) (Magma.srch8R68 v)).mpr hv)

/-- No member of the class satisfies any of these `24` equations. -/
theorem srch8R68_refutes_0 :
    FamilyRefutes Magma.srch8R68 [
      430, 442, 455, 1434, 1654, 1657, 1721, 1840, 1851, 1860, 2060, 3093, 3142, 3214, 3414,
      3526, 4023, 4135, 4315, 4339, 4357, 4615, 4645, 4689
    ] :=
  ⟨noS8R68_Law430, noS8R68_Law442, noS8R68_Law455, noS8R68_Law1434, noS8R68_Law1654, noS8R68_Law1657, noS8R68_Law1721, noS8R68_Law1840, noS8R68_Law1851, noS8R68_Law1860, noS8R68_Law2060, noS8R68_Law3093, noS8R68_Law3142, noS8R68_Law3214, noS8R68_Law3414, noS8R68_Law3526, noS8R68_Law4023, noS8R68_Law4135, noS8R68_Law4315, noS8R68_Law4339, noS8R68_Law4357, noS8R68_Law4615, noS8R68_Law4645, noS8R68_Law4689⟩
