import equational_theories.Definability.Srch_S8R75

/-!
# Structural certificate targets: `Magma.srch8R75`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R75_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `20` equations here, 520 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R75_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 466 takes them (28 nodes). -/
def ordS8R75_Law466 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 466. -/
theorem noS8R75_Law466 : ∀ v : Magma.tup8R75,
    ¬ @Equation466 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 837 takes them (5 nodes). -/
def ordS8R75_Law837 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 837. -/
theorem noS8R75_Law837 : ∀ v : Magma.tup8R75,
    ¬ @Equation837 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law837) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 3)
    (ord := ordS8R75_Law837) (by native_decide) v.1 v.2
    ((@Law837.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (27 nodes). -/
def ordS8R75_Law1075 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1075. -/
theorem noS8R75_Law1075 : ∀ v : Magma.tup8R75,
    ¬ @Equation1075 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1242 takes them (11 nodes). -/
def ordS8R75_Law1242 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1242. -/
theorem noS8R75_Law1242 : ∀ v : Magma.tup8R75,
    ¬ @Equation1242 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1242) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law1242) (by native_decide) v.1 v.2
    ((@Law1242.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1259 takes them (5 nodes). -/
def ordS8R75_Law1259 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1259. -/
theorem noS8R75_Law1259 : ∀ v : Magma.tup8R75,
    ¬ @Equation1259 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1259) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 3)
    (ord := ordS8R75_Law1259) (by native_decide) v.1 v.2
    ((@Law1259.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1442 takes them (19 nodes). -/
def ordS8R75_Law1442 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1442. -/
theorem noS8R75_Law1442 : ∀ v : Magma.tup8R75,
    ¬ @Equation1442 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1442) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law1442) (by native_decide) v.1 v.2
    ((@Law1442.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1444 takes them (40 nodes). -/
def ordS8R75_Law1444 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1444. -/
theorem noS8R75_Law1444 : ∀ v : Magma.tup8R75,
    ¬ @Equation1444 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1444) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law1444) (by native_decide) v.1 v.2
    ((@Law1444.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1654 takes them (59 nodes). -/
def ordS8R75_Law1654 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1654. -/
theorem noS8R75_Law1654 : ∀ v : Magma.tup8R75,
    ¬ @Equation1654 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1657 takes them (47 nodes). -/
def ordS8R75_Law1657 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1657. -/
theorem noS8R75_Law1657 : ∀ v : Magma.tup8R75,
    ¬ @Equation1657 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1657) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law1657) (by native_decide) v.1 v.2
    ((@Law1657.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1664 takes them (19 nodes). -/
def ordS8R75_Law1664 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1664. -/
theorem noS8R75_Law1664 : ∀ v : Magma.tup8R75,
    ¬ @Equation1664 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1664) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 3)
    (ord := ordS8R75_Law1664) (by native_decide) v.1 v.2
    ((@Law1664.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (59 nodes). -/
def ordS8R75_Law1840 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1840. -/
theorem noS8R75_Law1840 : ∀ v : Magma.tup8R75,
    ¬ @Equation1840 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1843 takes them (19 nodes). -/
def ordS8R75_Law1843 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1843. -/
theorem noS8R75_Law1843 : ∀ v : Magma.tup8R75,
    ¬ @Equation1843 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1843) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 3)
    (ord := ordS8R75_Law1843) (by native_decide) v.1 v.2
    ((@Law1843.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1860 takes them (47 nodes). -/
def ordS8R75_Law1860 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 1860. -/
theorem noS8R75_Law1860 : ∀ v : Magma.tup8R75,
    ¬ @Equation1860 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1860) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law1860) (by native_decide) v.1 v.2
    ((@Law1860.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (40 nodes). -/
def ordS8R75_Law2053 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2053. -/
theorem noS8R75_Law2053 : ∀ v : Magma.tup8R75,
    ¬ @Equation2053 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (19 nodes). -/
def ordS8R75_Law2090 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2090. -/
theorem noS8R75_Law2090 : ∀ v : Magma.tup8R75,
    ¬ @Equation2090 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2314 takes them (5 nodes). -/
def ordS8R75_Law2314 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2314. -/
theorem noS8R75_Law2314 : ∀ v : Magma.tup8R75,
    ¬ @Equation2314 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2314) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 3)
    (ord := ordS8R75_Law2314) (by native_decide) v.1 v.2
    ((@Law2314.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2330 takes them (11 nodes). -/
def ordS8R75_Law2330 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2330. -/
theorem noS8R75_Law2330 : ∀ v : Magma.tup8R75,
    ¬ @Equation2330 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2330) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law2330) (by native_decide) v.1 v.2
    ((@Law2330.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (27 nodes). -/
def ordS8R75_Law2457 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2457. -/
theorem noS8R75_Law2457 : ∀ v : Magma.tup8R75,
    ¬ @Equation2457 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2778 takes them (5 nodes). -/
def ordS8R75_Law2778 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 2778. -/
theorem noS8R75_Law2778 : ∀ v : Magma.tup8R75,
    ¬ @Equation2778 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2778) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 3)
    (ord := ordS8R75_Law2778) (by native_decide) v.1 v.2
    ((@Law2778.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (28 nodes). -/
def ordS8R75_Law3066 : List (Fin 4) := [0, 1, 2, 3]

/-- No member of the class satisfies equation 3066. -/
theorem noS8R75_Law3066 : ∀ v : Magma.tup8R75,
    ¬ @Equation3066 (Fin 8) (Magma.srch8R75 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S8R75.E) (tr := S8R75.tr) (z := S8R75.z)
    (st := S8R75.st) (X := S8R75.X) (envs := Magma.envsRed 8 S8R75.E 2)
    (ord := ordS8R75_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 8) (Magma.srch8R75 v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch8R75_refutes_0 :
    FamilyRefutes Magma.srch8R75 [
      466, 837, 1075, 1242, 1259, 1442, 1444, 1654, 1657, 1664, 1840, 1843, 1860, 2053, 2090,
      2314, 2330, 2457, 2778, 3066
    ] :=
  ⟨noS8R75_Law466, noS8R75_Law837, noS8R75_Law1075, noS8R75_Law1242, noS8R75_Law1259, noS8R75_Law1442, noS8R75_Law1444, noS8R75_Law1654, noS8R75_Law1657, noS8R75_Law1664, noS8R75_Law1840, noS8R75_Law1843, noS8R75_Law1860, noS8R75_Law2053, noS8R75_Law2090, noS8R75_Law2314, noS8R75_Law2330, noS8R75_Law2457, noS8R75_Law2778, noS8R75_Law3066⟩
