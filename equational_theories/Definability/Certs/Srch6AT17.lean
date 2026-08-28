import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 18 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `19`
equations here, 3,092 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1862 takes them (133 nodes). -/
def ordS6A_Law1862 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1862. -/
theorem noS6A_Law1862 : ∀ v : Magma.tupS6A,
    ¬ @Equation1862 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1862) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1862) (by native_decide) v.1 v.2
    ((@Law1862.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1864 takes them (155 nodes). -/
def ordS6A_Law1864 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1864. -/
theorem noS6A_Law1864 : ∀ v : Magma.tupS6A,
    ¬ @Equation1864 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1864) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1864) (by native_decide) v.1 v.2
    ((@Law1864.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1866 takes them (81 nodes). -/
def ordS6A_Law1866 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1866. -/
theorem noS6A_Law1866 : ∀ v : Magma.tupS6A,
    ¬ @Equation1866 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1866) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1866) (by native_decide) v.1 v.2
    ((@Law1866.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1868 takes them (201 nodes). -/
def ordS6A_Law1868 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1868. -/
theorem noS6A_Law1868 : ∀ v : Magma.tupS6A,
    ¬ @Equation1868 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1868) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1868) (by native_decide) v.1 v.2
    ((@Law1868.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1869 takes them (138 nodes). -/
def ordS6A_Law1869 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1869. -/
theorem noS6A_Law1869 : ∀ v : Magma.tupS6A,
    ¬ @Equation1869 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1869) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1869) (by native_decide) v.1 v.2
    ((@Law1869.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1870 takes them (73 nodes). -/
def ordS6A_Law1870 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1870. -/
theorem noS6A_Law1870 : ∀ v : Magma.tupS6A,
    ¬ @Equation1870 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1870) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1870) (by native_decide) v.1 v.2
    ((@Law1870.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1871 takes them (447 nodes). -/
def ordS6A_Law1871 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1871. -/
theorem noS6A_Law1871 : ∀ v : Magma.tupS6A,
    ¬ @Equation1871 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1871) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1871) (by native_decide) v.1 v.2
    ((@Law1871.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1872 takes them (209 nodes). -/
def ordS6A_Law1872 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1872. -/
theorem noS6A_Law1872 : ∀ v : Magma.tupS6A,
    ¬ @Equation1872 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1872) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1872) (by native_decide) v.1 v.2
    ((@Law1872.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1874 takes them (70 nodes). -/
def ordS6A_Law1874 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1874. -/
theorem noS6A_Law1874 : ∀ v : Magma.tupS6A,
    ¬ @Equation1874 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1874) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1874) (by native_decide) v.1 v.2
    ((@Law1874.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1875 takes them (452 nodes). -/
def ordS6A_Law1875 : List (Fin 11) := [5, 0, 10, 2, 4, 3, 7, 1, 9, 6, 8]

/-- No member of the class satisfies equation 1875. -/
theorem noS6A_Law1875 : ∀ v : Magma.tupS6A,
    ¬ @Equation1875 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1875) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1875) (by native_decide) v.1 v.2
    ((@Law1875.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1877 takes them (165 nodes). -/
def ordS6A_Law1877 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1877. -/
theorem noS6A_Law1877 : ∀ v : Magma.tupS6A,
    ¬ @Equation1877 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1877) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1877) (by native_decide) v.1 v.2
    ((@Law1877.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1878 takes them (56 nodes). -/
def ordS6A_Law1878 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1878. -/
theorem noS6A_Law1878 : ∀ v : Magma.tupS6A,
    ¬ @Equation1878 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1878) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1878) (by native_decide) v.1 v.2
    ((@Law1878.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1879 takes them (199 nodes). -/
def ordS6A_Law1879 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1879. -/
theorem noS6A_Law1879 : ∀ v : Magma.tupS6A,
    ¬ @Equation1879 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1879) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1879) (by native_decide) v.1 v.2
    ((@Law1879.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1880 takes them (95 nodes). -/
def ordS6A_Law1880 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1880. -/
theorem noS6A_Law1880 : ∀ v : Magma.tupS6A,
    ¬ @Equation1880 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1880) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1880) (by native_decide) v.1 v.2
    ((@Law1880.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1881 takes them (86 nodes). -/
def ordS6A_Law1881 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1881. -/
theorem noS6A_Law1881 : ∀ v : Magma.tupS6A,
    ¬ @Equation1881 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1881) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1881) (by native_decide) v.1 v.2
    ((@Law1881.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1882 takes them (136 nodes). -/
def ordS6A_Law1882 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1882. -/
theorem noS6A_Law1882 : ∀ v : Magma.tupS6A,
    ¬ @Equation1882 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1882) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law1882) (by native_decide) v.1 v.2
    ((@Law1882.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1883 takes them (54 nodes). -/
def ordS6A_Law1883 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1883. -/
theorem noS6A_Law1883 : ∀ v : Magma.tupS6A,
    ¬ @Equation1883 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1883) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law1883) (by native_decide) v.1 v.2
    ((@Law1883.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1890 takes them (225 nodes). -/
def ordS6A_Law1890 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1890. -/
theorem noS6A_Law1890 : ∀ v : Magma.tupS6A,
    ¬ @Equation1890 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1890) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1890) (by native_decide) v.1 v.2
    ((@Law1890.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1900 takes them (117 nodes). -/
def ordS6A_Law1900 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 1900. -/
theorem noS6A_Law1900 : ∀ v : Magma.tupS6A,
    ¬ @Equation1900 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1900) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law1900) (by native_decide) v.1 v.2
    ((@Law1900.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `19` equations. -/
theorem srch6A_refutes_17 :
    FamilyRefutes Magma.srch6A [
      1862, 1864, 1866, 1868, 1869, 1870, 1871, 1872, 1874, 1875, 1877, 1878, 1879, 1880, 1881,
      1882, 1883, 1890, 1900
    ] :=
  ⟨noS6A_Law1862, noS6A_Law1864, noS6A_Law1866, noS6A_Law1868, noS6A_Law1869, noS6A_Law1870, noS6A_Law1871, noS6A_Law1872, noS6A_Law1874, noS6A_Law1875, noS6A_Law1877, noS6A_Law1878, noS6A_Law1879, noS6A_Law1880, noS6A_Law1881, noS6A_Law1882, noS6A_Law1883, noS6A_Law1890, noS6A_Law1900⟩
