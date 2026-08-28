import equational_theories.Definability.Srch_S9R205

/-!
# Structural certificate targets: `Magma.srch9R205` (part 2 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R205_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `91` equations here, 351 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R205_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1655 takes them (3 nodes). -/
def ordS9R205_Law1655 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1655. -/
theorem noS9R205_Law1655 : ∀ v : Magma.tup9R205,
    ¬ @Equation1655 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1655) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1655) (by native_decide) v.1 v.2
    ((@Law1655.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1657 takes them (4 nodes). -/
def ordS9R205_Law1657 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1657. -/
theorem noS9R205_Law1657 : ∀ v : Magma.tup9R205,
    ¬ @Equation1657 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1657) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1657) (by native_decide) v.1 v.2
    ((@Law1657.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1658 takes them (4 nodes). -/
def ordS9R205_Law1658 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1658. -/
theorem noS9R205_Law1658 : ∀ v : Magma.tup9R205,
    ¬ @Equation1658 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1658) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1658) (by native_decide) v.1 v.2
    ((@Law1658.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1662 takes them (4 nodes). -/
def ordS9R205_Law1662 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1662. -/
theorem noS9R205_Law1662 : ∀ v : Magma.tup9R205,
    ¬ @Equation1662 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1662) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law1662) (by native_decide) v.1 v.2
    ((@Law1662.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1684 takes them (4 nodes). -/
def ordS9R205_Law1684 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1684. -/
theorem noS9R205_Law1684 : ∀ v : Magma.tup9R205,
    ¬ @Equation1684 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1684) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1684) (by native_decide) v.1 v.2
    ((@Law1684.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1691 takes them (4 nodes). -/
def ordS9R205_Law1691 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1691. -/
theorem noS9R205_Law1691 : ∀ v : Magma.tup9R205,
    ¬ @Equation1691 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1691) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1691) (by native_decide) v.1 v.2
    ((@Law1691.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1731 takes them (4 nodes). -/
def ordS9R205_Law1731 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1731. -/
theorem noS9R205_Law1731 : ∀ v : Magma.tup9R205,
    ¬ @Equation1731 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1731) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1731) (by native_decide) v.1 v.2
    ((@Law1731.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1780 takes them (4 nodes). -/
def ordS9R205_Law1780 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1780. -/
theorem noS9R205_Law1780 : ∀ v : Magma.tup9R205,
    ¬ @Equation1780 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1780) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law1780) (by native_decide) v.1 v.2
    ((@Law1780.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1838 takes them (4 nodes). -/
def ordS9R205_Law1838 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1838. -/
theorem noS9R205_Law1838 : ∀ v : Magma.tup9R205,
    ¬ @Equation1838 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1838) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1838) (by native_decide) v.1 v.2
    ((@Law1838.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1840 takes them (5 nodes). -/
def ordS9R205_Law1840 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1840. -/
theorem noS9R205_Law1840 : ∀ v : Magma.tup9R205,
    ¬ @Equation1840 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1848 takes them (4 nodes). -/
def ordS9R205_Law1848 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1848. -/
theorem noS9R205_Law1848 : ∀ v : Magma.tup9R205,
    ¬ @Equation1848 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1848) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1848) (by native_decide) v.1 v.2
    ((@Law1848.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1850 takes them (5 nodes). -/
def ordS9R205_Law1850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1850. -/
theorem noS9R205_Law1850 : ∀ v : Magma.tup9R205,
    ¬ @Equation1850 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1850) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1850) (by native_decide) v.1 v.2
    ((@Law1850.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1860 takes them (4 nodes). -/
def ordS9R205_Law1860 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1860. -/
theorem noS9R205_Law1860 : ∀ v : Magma.tup9R205,
    ¬ @Equation1860 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1860) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1860) (by native_decide) v.1 v.2
    ((@Law1860.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1861 takes them (4 nodes). -/
def ordS9R205_Law1861 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1861. -/
theorem noS9R205_Law1861 : ∀ v : Magma.tup9R205,
    ¬ @Equation1861 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1861) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1861) (by native_decide) v.1 v.2
    ((@Law1861.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1873 takes them (4 nodes). -/
def ordS9R205_Law1873 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1873. -/
theorem noS9R205_Law1873 : ∀ v : Magma.tup9R205,
    ¬ @Equation1873 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1873) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law1873) (by native_decide) v.1 v.2
    ((@Law1873.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1894 takes them (4 nodes). -/
def ordS9R205_Law1894 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1894. -/
theorem noS9R205_Law1894 : ∀ v : Magma.tup9R205,
    ¬ @Equation1894 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1894) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1894) (by native_decide) v.1 v.2
    ((@Law1894.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1897 takes them (3 nodes). -/
def ordS9R205_Law1897 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1897. -/
theorem noS9R205_Law1897 : ∀ v : Magma.tup9R205,
    ¬ @Equation1897 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1897) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1897) (by native_decide) v.1 v.2
    ((@Law1897.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1921 takes them (4 nodes). -/
def ordS9R205_Law1921 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1921. -/
theorem noS9R205_Law1921 : ∀ v : Magma.tup9R205,
    ¬ @Equation1921 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1921) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1921) (by native_decide) v.1 v.2
    ((@Law1921.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1934 takes them (4 nodes). -/
def ordS9R205_Law1934 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1934. -/
theorem noS9R205_Law1934 : ∀ v : Magma.tup9R205,
    ¬ @Equation1934 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (4 nodes). -/
def ordS9R205_Law1949 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1949. -/
theorem noS9R205_Law1949 : ∀ v : Magma.tup9R205,
    ¬ @Equation1949 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2043 takes them (4 nodes). -/
def ordS9R205_Law2043 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2043. -/
theorem noS9R205_Law2043 : ∀ v : Magma.tup9R205,
    ¬ @Equation2043 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2043) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2043) (by native_decide) v.1 v.2
    ((@Law2043.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2044 takes them (4 nodes). -/
def ordS9R205_Law2044 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2044. -/
theorem noS9R205_Law2044 : ∀ v : Magma.tup9R205,
    ¬ @Equation2044 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2044) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2044) (by native_decide) v.1 v.2
    ((@Law2044.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2051 takes them (4 nodes). -/
def ordS9R205_Law2051 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2051. -/
theorem noS9R205_Law2051 : ∀ v : Magma.tup9R205,
    ¬ @Equation2051 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2051) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2051) (by native_decide) v.1 v.2
    ((@Law2051.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2053 takes them (5 nodes). -/
def ordS9R205_Law2053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2053. -/
theorem noS9R205_Law2053 : ∀ v : Magma.tup9R205,
    ¬ @Equation2053 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2053) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2053) (by native_decide) v.1 v.2
    ((@Law2053.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2060 takes them (5 nodes). -/
def ordS9R205_Law2060 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2060. -/
theorem noS9R205_Law2060 : ∀ v : Magma.tup9R205,
    ¬ @Equation2060 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2060) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2060) (by native_decide) v.1 v.2
    ((@Law2060.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2064 takes them (3 nodes). -/
def ordS9R205_Law2064 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2064. -/
theorem noS9R205_Law2064 : ∀ v : Magma.tup9R205,
    ¬ @Equation2064 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2064) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2064) (by native_decide) v.1 v.2
    ((@Law2064.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2090 takes them (4 nodes). -/
def ordS9R205_Law2090 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2090. -/
theorem noS9R205_Law2090 : ∀ v : Magma.tup9R205,
    ¬ @Equation2090 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2090) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2090) (by native_decide) v.1 v.2
    ((@Law2090.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2097 takes them (4 nodes). -/
def ordS9R205_Law2097 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2097. -/
theorem noS9R205_Law2097 : ∀ v : Magma.tup9R205,
    ¬ @Equation2097 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2097) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2097) (by native_decide) v.1 v.2
    ((@Law2097.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2128 takes them (3 nodes). -/
def ordS9R205_Law2128 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2128. -/
theorem noS9R205_Law2128 : ∀ v : Magma.tup9R205,
    ¬ @Equation2128 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2128) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2128) (by native_decide) v.1 v.2
    ((@Law2128.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2137 takes them (4 nodes). -/
def ordS9R205_Law2137 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2137. -/
theorem noS9R205_Law2137 : ∀ v : Magma.tup9R205,
    ¬ @Equation2137 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2137) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2137) (by native_decide) v.1 v.2
    ((@Law2137.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2247 takes them (3 nodes). -/
def ordS9R205_Law2247 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2247. -/
theorem noS9R205_Law2247 : ∀ v : Magma.tup9R205,
    ¬ @Equation2247 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2247) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2247) (by native_decide) v.1 v.2
    ((@Law2247.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2256 takes them (5 nodes). -/
def ordS9R205_Law2256 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2256. -/
theorem noS9R205_Law2256 : ∀ v : Magma.tup9R205,
    ¬ @Equation2256 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2256) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2256) (by native_decide) v.1 v.2
    ((@Law2256.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2263 takes them (5 nodes). -/
def ordS9R205_Law2263 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2263. -/
theorem noS9R205_Law2263 : ∀ v : Magma.tup9R205,
    ¬ @Equation2263 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2263) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2263) (by native_decide) v.1 v.2
    ((@Law2263.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (4 nodes). -/
def ordS9R205_Law2267 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2267. -/
theorem noS9R205_Law2267 : ∀ v : Magma.tup9R205,
    ¬ @Equation2267 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2293 takes them (3 nodes). -/
def ordS9R205_Law2293 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2293. -/
theorem noS9R205_Law2293 : ∀ v : Magma.tup9R205,
    ¬ @Equation2293 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2293) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2293) (by native_decide) v.1 v.2
    ((@Law2293.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2300 takes them (3 nodes). -/
def ordS9R205_Law2300 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2300. -/
theorem noS9R205_Law2300 : ∀ v : Magma.tup9R205,
    ¬ @Equation2300 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2300) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2300) (by native_decide) v.1 v.2
    ((@Law2300.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2303 takes them (4 nodes). -/
def ordS9R205_Law2303 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2303. -/
theorem noS9R205_Law2303 : ∀ v : Magma.tup9R205,
    ¬ @Equation2303 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2303) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2303) (by native_decide) v.1 v.2
    ((@Law2303.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2327 takes them (4 nodes). -/
def ordS9R205_Law2327 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2327. -/
theorem noS9R205_Law2327 : ∀ v : Magma.tup9R205,
    ¬ @Equation2327 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2327) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2327) (by native_decide) v.1 v.2
    ((@Law2327.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2330 takes them (3 nodes). -/
def ordS9R205_Law2330 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2330. -/
theorem noS9R205_Law2330 : ∀ v : Magma.tup9R205,
    ¬ @Equation2330 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2330) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2330) (by native_decide) v.1 v.2
    ((@Law2330.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2337 takes them (3 nodes). -/
def ordS9R205_Law2337 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2337. -/
theorem noS9R205_Law2337 : ∀ v : Magma.tup9R205,
    ¬ @Equation2337 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2337) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2337) (by native_decide) v.1 v.2
    ((@Law2337.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2444 takes them (3 nodes). -/
def ordS9R205_Law2444 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2444. -/
theorem noS9R205_Law2444 : ∀ v : Magma.tup9R205,
    ¬ @Equation2444 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2444) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2444) (by native_decide) v.1 v.2
    ((@Law2444.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2449 takes them (5 nodes). -/
def ordS9R205_Law2449 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2449. -/
theorem noS9R205_Law2449 : ∀ v : Magma.tup9R205,
    ¬ @Equation2449 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2449) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2449) (by native_decide) v.1 v.2
    ((@Law2449.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (4 nodes). -/
def ordS9R205_Law2457 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2457. -/
theorem noS9R205_Law2457 : ∀ v : Magma.tup9R205,
    ¬ @Equation2457 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2459 takes them (5 nodes). -/
def ordS9R205_Law2459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2459. -/
theorem noS9R205_Law2459 : ∀ v : Magma.tup9R205,
    ¬ @Equation2459 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2459) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2459) (by native_decide) v.1 v.2
    ((@Law2459.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2470 takes them (4 nodes). -/
def ordS9R205_Law2470 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2470. -/
theorem noS9R205_Law2470 : ∀ v : Magma.tup9R205,
    ¬ @Equation2470 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2470) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2470) (by native_decide) v.1 v.2
    ((@Law2470.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2485 takes them (4 nodes). -/
def ordS9R205_Law2485 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2485. -/
theorem noS9R205_Law2485 : ∀ v : Magma.tup9R205,
    ¬ @Equation2485 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2496 takes them (4 nodes). -/
def ordS9R205_Law2496 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2496. -/
theorem noS9R205_Law2496 : ∀ v : Magma.tup9R205,
    ¬ @Equation2496 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2496) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2496) (by native_decide) v.1 v.2
    ((@Law2496.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2506 takes them (3 nodes). -/
def ordS9R205_Law2506 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2506. -/
theorem noS9R205_Law2506 : ∀ v : Magma.tup9R205,
    ¬ @Equation2506 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2506) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2506) (by native_decide) v.1 v.2
    ((@Law2506.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2530 takes them (3 nodes). -/
def ordS9R205_Law2530 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2530. -/
theorem noS9R205_Law2530 : ∀ v : Magma.tup9R205,
    ¬ @Equation2530 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2530) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2530) (by native_decide) v.1 v.2
    ((@Law2530.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2533 takes them (3 nodes). -/
def ordS9R205_Law2533 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2533. -/
theorem noS9R205_Law2533 : ∀ v : Magma.tup9R205,
    ¬ @Equation2533 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2533) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2533) (by native_decide) v.1 v.2
    ((@Law2533.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2534 takes them (3 nodes). -/
def ordS9R205_Law2534 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2534. -/
theorem noS9R205_Law2534 : ∀ v : Magma.tup9R205,
    ¬ @Equation2534 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2534) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2534) (by native_decide) v.1 v.2
    ((@Law2534.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2540 takes them (4 nodes). -/
def ordS9R205_Law2540 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2540. -/
theorem noS9R205_Law2540 : ∀ v : Magma.tup9R205,
    ¬ @Equation2540 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2540) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2540) (by native_decide) v.1 v.2
    ((@Law2540.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2647 takes them (3 nodes). -/
def ordS9R205_Law2647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2647. -/
theorem noS9R205_Law2647 : ∀ v : Magma.tup9R205,
    ¬ @Equation2647 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2647) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2647) (by native_decide) v.1 v.2
    ((@Law2647.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2653 takes them (4 nodes). -/
def ordS9R205_Law2653 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2653. -/
theorem noS9R205_Law2653 : ∀ v : Magma.tup9R205,
    ¬ @Equation2653 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2653) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2653) (by native_decide) v.1 v.2
    ((@Law2653.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2660 takes them (3 nodes). -/
def ordS9R205_Law2660 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2660. -/
theorem noS9R205_Law2660 : ∀ v : Magma.tup9R205,
    ¬ @Equation2660 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2660) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2660) (by native_decide) v.1 v.2
    ((@Law2660.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2663 takes them (4 nodes). -/
def ordS9R205_Law2663 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2663. -/
theorem noS9R205_Law2663 : ∀ v : Magma.tup9R205,
    ¬ @Equation2663 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2663) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2663) (by native_decide) v.1 v.2
    ((@Law2663.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2669 takes them (4 nodes). -/
def ordS9R205_Law2669 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2669. -/
theorem noS9R205_Law2669 : ∀ v : Magma.tup9R205,
    ¬ @Equation2669 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2669) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2669) (by native_decide) v.1 v.2
    ((@Law2669.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2672 takes them (5 nodes). -/
def ordS9R205_Law2672 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2672. -/
theorem noS9R205_Law2672 : ∀ v : Magma.tup9R205,
    ¬ @Equation2672 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2672) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2672) (by native_decide) v.1 v.2
    ((@Law2672.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2673 takes them (3 nodes). -/
def ordS9R205_Law2673 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2673. -/
theorem noS9R205_Law2673 : ∀ v : Magma.tup9R205,
    ¬ @Equation2673 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2673) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2673) (by native_decide) v.1 v.2
    ((@Law2673.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2709 takes them (4 nodes). -/
def ordS9R205_Law2709 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2709. -/
theorem noS9R205_Law2709 : ∀ v : Magma.tup9R205,
    ¬ @Equation2709 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2709) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2709) (by native_decide) v.1 v.2
    ((@Law2709.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2736 takes them (4 nodes). -/
def ordS9R205_Law2736 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2736. -/
theorem noS9R205_Law2736 : ∀ v : Magma.tup9R205,
    ¬ @Equation2736 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2736) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2736) (by native_decide) v.1 v.2
    ((@Law2736.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2743 takes them (4 nodes). -/
def ordS9R205_Law2743 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2743. -/
theorem noS9R205_Law2743 : ∀ v : Magma.tup9R205,
    ¬ @Equation2743 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2743) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2743) (by native_decide) v.1 v.2
    ((@Law2743.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (4 nodes). -/
def ordS9R205_Law2850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2850. -/
theorem noS9R205_Law2850 : ∀ v : Magma.tup9R205,
    ¬ @Equation2850 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2855 takes them (4 nodes). -/
def ordS9R205_Law2855 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2855. -/
theorem noS9R205_Law2855 : ∀ v : Magma.tup9R205,
    ¬ @Equation2855 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2855) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2855) (by native_decide) v.1 v.2
    ((@Law2855.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2863 takes them (4 nodes). -/
def ordS9R205_Law2863 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2863. -/
theorem noS9R205_Law2863 : ∀ v : Magma.tup9R205,
    ¬ @Equation2863 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2863) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2863) (by native_decide) v.1 v.2
    ((@Law2863.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2873 takes them (3 nodes). -/
def ordS9R205_Law2873 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2873. -/
theorem noS9R205_Law2873 : ∀ v : Magma.tup9R205,
    ¬ @Equation2873 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2873) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2873) (by native_decide) v.1 v.2
    ((@Law2873.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2875 takes them (5 nodes). -/
def ordS9R205_Law2875 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2875. -/
theorem noS9R205_Law2875 : ∀ v : Magma.tup9R205,
    ¬ @Equation2875 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2875) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2875) (by native_decide) v.1 v.2
    ((@Law2875.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2876 takes them (3 nodes). -/
def ordS9R205_Law2876 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2876. -/
theorem noS9R205_Law2876 : ∀ v : Magma.tup9R205,
    ¬ @Equation2876 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2876) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2876) (by native_decide) v.1 v.2
    ((@Law2876.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2902 takes them (4 nodes). -/
def ordS9R205_Law2902 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2902. -/
theorem noS9R205_Law2902 : ∀ v : Magma.tup9R205,
    ¬ @Equation2902 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2902) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2902) (by native_decide) v.1 v.2
    ((@Law2902.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2909 takes them (4 nodes). -/
def ordS9R205_Law2909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2909. -/
theorem noS9R205_Law2909 : ∀ v : Magma.tup9R205,
    ¬ @Equation2909 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2936 takes them (4 nodes). -/
def ordS9R205_Law2936 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2936. -/
theorem noS9R205_Law2936 : ∀ v : Magma.tup9R205,
    ¬ @Equation2936 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2936) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law2936) (by native_decide) v.1 v.2
    ((@Law2936.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (4 nodes). -/
def ordS9R205_Law3053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3053. -/
theorem noS9R205_Law3053 : ∀ v : Magma.tup9R205,
    ¬ @Equation3053 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3056 takes them (3 nodes). -/
def ordS9R205_Law3056 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3056. -/
theorem noS9R205_Law3056 : ∀ v : Magma.tup9R205,
    ¬ @Equation3056 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3056) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3056) (by native_decide) v.1 v.2
    ((@Law3056.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3058 takes them (5 nodes). -/
def ordS9R205_Law3058 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3058. -/
theorem noS9R205_Law3058 : ∀ v : Magma.tup9R205,
    ¬ @Equation3058 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3058) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3058) (by native_decide) v.1 v.2
    ((@Law3058.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3059 takes them (3 nodes). -/
def ordS9R205_Law3059 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3059. -/
theorem noS9R205_Law3059 : ∀ v : Magma.tup9R205,
    ¬ @Equation3059 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3059) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3059) (by native_decide) v.1 v.2
    ((@Law3059.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (4 nodes). -/
def ordS9R205_Law3066 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3066. -/
theorem noS9R205_Law3066 : ∀ v : Magma.tup9R205,
    ¬ @Equation3066 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3068 takes them (4 nodes). -/
def ordS9R205_Law3068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3068. -/
theorem noS9R205_Law3068 : ∀ v : Magma.tup9R205,
    ¬ @Equation3068 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3068) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3068) (by native_decide) v.1 v.2
    ((@Law3068.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3075 takes them (5 nodes). -/
def ordS9R205_Law3075 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3075. -/
theorem noS9R205_Law3075 : ∀ v : Magma.tup9R205,
    ¬ @Equation3075 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3075) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3075) (by native_decide) v.1 v.2
    ((@Law3075.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3078 takes them (4 nodes). -/
def ordS9R205_Law3078 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3078. -/
theorem noS9R205_Law3078 : ∀ v : Magma.tup9R205,
    ¬ @Equation3078 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3078) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3078) (by native_decide) v.1 v.2
    ((@Law3078.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (4 nodes). -/
def ordS9R205_Law3083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3083. -/
theorem noS9R205_Law3083 : ∀ v : Magma.tup9R205,
    ¬ @Equation3083 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (3 nodes). -/
def ordS9R205_Law3091 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3091. -/
theorem noS9R205_Law3091 : ∀ v : Magma.tup9R205,
    ¬ @Equation3091 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (4 nodes). -/
def ordS9R205_Law3094 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3094. -/
theorem noS9R205_Law3094 : ∀ v : Magma.tup9R205,
    ¬ @Equation3094 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3105 takes them (3 nodes). -/
def ordS9R205_Law3105 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3105. -/
theorem noS9R205_Law3105 : ∀ v : Magma.tup9R205,
    ¬ @Equation3105 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3105) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3105) (by native_decide) v.1 v.2
    ((@Law3105.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (4 nodes). -/
def ordS9R205_Law3112 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3112. -/
theorem noS9R205_Law3112 : ∀ v : Magma.tup9R205,
    ¬ @Equation3112 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3115 takes them (3 nodes). -/
def ordS9R205_Law3115 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3115. -/
theorem noS9R205_Law3115 : ∀ v : Magma.tup9R205,
    ¬ @Equation3115 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3115) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3115) (by native_decide) v.1 v.2
    ((@Law3115.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (4 nodes). -/
def ordS9R205_Law3142 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3142. -/
theorem noS9R205_Law3142 : ∀ v : Magma.tup9R205,
    ¬ @Equation3142 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3259 takes them (4 nodes). -/
def ordS9R205_Law3259 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3259. -/
theorem noS9R205_Law3259 : ∀ v : Magma.tup9R205,
    ¬ @Equation3259 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3259) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3259) (by native_decide) v.1 v.2
    ((@Law3259.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3261 takes them (5 nodes). -/
def ordS9R205_Law3261 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3261. -/
theorem noS9R205_Law3261 : ∀ v : Magma.tup9R205,
    ¬ @Equation3261 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3261) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3261) (by native_decide) v.1 v.2
    ((@Law3261.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3272 takes them (3 nodes). -/
def ordS9R205_Law3272 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3272. -/
theorem noS9R205_Law3272 : ∀ v : Magma.tup9R205,
    ¬ @Equation3272 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3272) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3272) (by native_decide) v.1 v.2
    ((@Law3272.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3278 takes them (4 nodes). -/
def ordS9R205_Law3278 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3278. -/
theorem noS9R205_Law3278 : ∀ v : Magma.tup9R205,
    ¬ @Equation3278 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3278) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3278) (by native_decide) v.1 v.2
    ((@Law3278.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3281 takes them (3 nodes). -/
def ordS9R205_Law3281 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3281. -/
theorem noS9R205_Law3281 : ∀ v : Magma.tup9R205,
    ¬ @Equation3281 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3281) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3281) (by native_decide) v.1 v.2
    ((@Law3281.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- No member of the class satisfies any of these `91` equations. -/
theorem srch9R205_refutes_1 :
    FamilyRefutes Magma.srch9R205 [
      1655, 1657, 1658, 1662, 1684, 1691, 1731, 1780, 1838, 1840, 1848, 1850, 1860, 1861, 1873,
      1894, 1897, 1921, 1934, 1949, 2043, 2044, 2051, 2053, 2060, 2064, 2090, 2097, 2128, 2137,
      2247, 2256, 2263, 2267, 2293, 2300, 2303, 2327, 2330, 2337, 2444, 2449, 2457, 2459, 2470,
      2485, 2496, 2506, 2530, 2533, 2534, 2540, 2647, 2653, 2660, 2663, 2669, 2672, 2673, 2709,
      2736, 2743, 2850, 2855, 2863, 2873, 2875, 2876, 2902, 2909, 2936, 3053, 3056, 3058, 3059,
      3066, 3068, 3075, 3078, 3083, 3091, 3094, 3105, 3112, 3115, 3142, 3259, 3261, 3272, 3278,
      3281
    ] :=
  ⟨noS9R205_Law1655, noS9R205_Law1657, noS9R205_Law1658, noS9R205_Law1662, noS9R205_Law1684, noS9R205_Law1691, noS9R205_Law1731, noS9R205_Law1780, noS9R205_Law1838, noS9R205_Law1840, noS9R205_Law1848, noS9R205_Law1850, noS9R205_Law1860, noS9R205_Law1861, noS9R205_Law1873, noS9R205_Law1894, noS9R205_Law1897, noS9R205_Law1921, noS9R205_Law1934, noS9R205_Law1949, noS9R205_Law2043, noS9R205_Law2044, noS9R205_Law2051, noS9R205_Law2053, noS9R205_Law2060, noS9R205_Law2064, noS9R205_Law2090, noS9R205_Law2097, noS9R205_Law2128, noS9R205_Law2137, noS9R205_Law2247, noS9R205_Law2256, noS9R205_Law2263, noS9R205_Law2267, noS9R205_Law2293, noS9R205_Law2300, noS9R205_Law2303, noS9R205_Law2327, noS9R205_Law2330, noS9R205_Law2337, noS9R205_Law2444, noS9R205_Law2449, noS9R205_Law2457, noS9R205_Law2459, noS9R205_Law2470, noS9R205_Law2485, noS9R205_Law2496, noS9R205_Law2506, noS9R205_Law2530, noS9R205_Law2533, noS9R205_Law2534, noS9R205_Law2540, noS9R205_Law2647, noS9R205_Law2653, noS9R205_Law2660, noS9R205_Law2663, noS9R205_Law2669, noS9R205_Law2672, noS9R205_Law2673, noS9R205_Law2709, noS9R205_Law2736, noS9R205_Law2743, noS9R205_Law2850, noS9R205_Law2855, noS9R205_Law2863, noS9R205_Law2873, noS9R205_Law2875, noS9R205_Law2876, noS9R205_Law2902, noS9R205_Law2909, noS9R205_Law2936, noS9R205_Law3053, noS9R205_Law3056, noS9R205_Law3058, noS9R205_Law3059, noS9R205_Law3066, noS9R205_Law3068, noS9R205_Law3075, noS9R205_Law3078, noS9R205_Law3083, noS9R205_Law3091, noS9R205_Law3094, noS9R205_Law3105, noS9R205_Law3112, noS9R205_Law3115, noS9R205_Law3142, noS9R205_Law3259, noS9R205_Law3261, noS9R205_Law3272, noS9R205_Law3278, noS9R205_Law3281⟩
