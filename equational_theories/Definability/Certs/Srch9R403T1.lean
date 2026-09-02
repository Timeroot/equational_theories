import equational_theories.Definability.Srch_S9R403

/-!
# Structural certificate targets: `Magma.srch9R403` (part 2 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R403_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,125 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R403_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1654 takes them (525 nodes). -/
def ordS9R403_Law1654 : List (Fin 7) := [6, 4, 2, 1, 5, 3, 0]

/-- No member of the class satisfies equation 1654. -/
theorem noS9R403_Law1654 : ∀ v : Magma.tup9R403,
    ¬ @Equation1654 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1654) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1654) (by native_decide) v.1 v.2
    ((@Law1654.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1658 takes them (112 nodes). -/
def ordS9R403_Law1658 : List (Fin 7) := [2, 0, 6, 5, 1, 3, 4]

/-- No member of the class satisfies equation 1658. -/
theorem noS9R403_Law1658 : ∀ v : Magma.tup9R403,
    ¬ @Equation1658 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1658) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1658) (by native_decide) v.1 v.2
    ((@Law1658.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1662 takes them (289 nodes). -/
def ordS9R403_Law1662 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1662. -/
theorem noS9R403_Law1662 : ∀ v : Magma.tup9R403,
    ¬ @Equation1662 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1662) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law1662) (by native_decide) v.1 v.2
    ((@Law1662.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1664 takes them (182 nodes). -/
def ordS9R403_Law1664 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1664. -/
theorem noS9R403_Law1664 : ∀ v : Magma.tup9R403,
    ¬ @Equation1664 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1664) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law1664) (by native_decide) v.1 v.2
    ((@Law1664.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1780 takes them (130 nodes). -/
def ordS9R403_Law1780 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1780. -/
theorem noS9R403_Law1780 : ∀ v : Magma.tup9R403,
    ¬ @Equation1780 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1780) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law1780) (by native_decide) v.1 v.2
    ((@Law1780.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (515 nodes). -/
def ordS9R403_Law1840 : List (Fin 7) := [5, 6, 1, 3, 4, 0, 2]

/-- No member of the class satisfies equation 1840. -/
theorem noS9R403_Law1840 : ∀ v : Magma.tup9R403,
    ¬ @Equation1840 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1843 takes them (198 nodes). -/
def ordS9R403_Law1843 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1843. -/
theorem noS9R403_Law1843 : ∀ v : Magma.tup9R403,
    ¬ @Equation1843 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1843) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law1843) (by native_decide) v.1 v.2
    ((@Law1843.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1873 takes them (289 nodes). -/
def ordS9R403_Law1873 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1873. -/
theorem noS9R403_Law1873 : ∀ v : Magma.tup9R403,
    ¬ @Equation1873 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1873) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law1873) (by native_decide) v.1 v.2
    ((@Law1873.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1887 takes them (341 nodes). -/
def ordS9R403_Law1887 : List (Fin 7) := [0, 2, 1, 3, 5, 4, 6]

/-- No member of the class satisfies equation 1887. -/
theorem noS9R403_Law1887 : ∀ v : Magma.tup9R403,
    ¬ @Equation1887 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1887) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1887) (by native_decide) v.1 v.2
    ((@Law1887.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1934 takes them (123 nodes). -/
def ordS9R403_Law1934 : List (Fin 7) := [1, 5, 6, 0, 2, 4, 3]

/-- No member of the class satisfies equation 1934. -/
theorem noS9R403_Law1934 : ∀ v : Magma.tup9R403,
    ¬ @Equation1934 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (187 nodes). -/
def ordS9R403_Law1949 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1949. -/
theorem noS9R403_Law1949 : ∀ v : Magma.tup9R403,
    ¬ @Equation1949 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (234 nodes). -/
def ordS9R403_Law2137 : List (Fin 7) := [6, 0, 1, 4, 2, 5, 3]

/-- No member of the class satisfies equation 2137. -/
theorem noS9R403_Law2137 : ∀ v : Magma.tup9R403,
    ¬ @Equation2137 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch9R403_refutes_1 :
    FamilyRefutes Magma.srch9R403 [
      1654, 1658, 1662, 1664, 1780, 1840, 1843, 1873, 1887, 1934, 1949, 2137
    ] :=
  ⟨noS9R403_Law1654, noS9R403_Law1658, noS9R403_Law1662, noS9R403_Law1664, noS9R403_Law1780, noS9R403_Law1840, noS9R403_Law1843, noS9R403_Law1873, noS9R403_Law1887, noS9R403_Law1934, noS9R403_Law1949, noS9R403_Law2137⟩
