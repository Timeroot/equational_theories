import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 21 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 3,083 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1863 takes them (357 nodes). -/
def ordS7R12_Law1863 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1863. -/
theorem noS7R12_Law1863 : ∀ v : Magma.tup7R12,
    ¬ @Equation1863 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1863) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1863) (by native_decide) v.1 v.2
    ((@Law1863.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1867 takes them (503 nodes). -/
def ordS7R12_Law1867 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1867. -/
theorem noS7R12_Law1867 : ∀ v : Magma.tup7R12,
    ¬ @Equation1867 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1867) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1867) (by native_decide) v.1 v.2
    ((@Law1867.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1873 takes them (385 nodes). -/
def ordS7R12_Law1873 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1873. -/
theorem noS7R12_Law1873 : ∀ v : Magma.tup7R12,
    ¬ @Equation1873 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1873) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1873) (by native_decide) v.1 v.2
    ((@Law1873.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1887 takes them (421 nodes). -/
def ordS7R12_Law1887 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1887. -/
theorem noS7R12_Law1887 : ∀ v : Magma.tup7R12,
    ¬ @Equation1887 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1887) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1887) (by native_decide) v.1 v.2
    ((@Law1887.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1897 takes them (282 nodes). -/
def ordS7R12_Law1897 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1897. -/
theorem noS7R12_Law1897 : ∀ v : Magma.tup7R12,
    ¬ @Equation1897 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1897) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1897) (by native_decide) v.1 v.2
    ((@Law1897.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1934 takes them (579 nodes). -/
def ordS7R12_Law1934 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1934. -/
theorem noS7R12_Law1934 : ∀ v : Magma.tup7R12,
    ¬ @Equation1934 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1934) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law1934) (by native_decide) v.1 v.2
    ((@Law1934.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1949 takes them (231 nodes). -/
def ordS7R12_Law1949 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1949. -/
theorem noS7R12_Law1949 : ∀ v : Magma.tup7R12,
    ¬ @Equation1949 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1949) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1949) (by native_decide) v.1 v.2
    ((@Law1949.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1958 takes them (167 nodes). -/
def ordS7R12_Law1958 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1958. -/
theorem noS7R12_Law1958 : ∀ v : Magma.tup7R12,
    ¬ @Equation1958 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1958) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1958) (by native_decide) v.1 v.2
    ((@Law1958.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1975 takes them (158 nodes). -/
def ordS7R12_Law1975 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1975. -/
theorem noS7R12_Law1975 : ∀ v : Magma.tup7R12,
    ¬ @Equation1975 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1975) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law1975) (by native_decide) v.1 v.2
    ((@Law1975.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch7R12_refutes_20 :
    FamilyRefutes Magma.srch7R12 [
      1863, 1867, 1873, 1887, 1897, 1934, 1949, 1958, 1975
    ] :=
  ⟨noS7R12_Law1863, noS7R12_Law1867, noS7R12_Law1873, noS7R12_Law1887, noS7R12_Law1897, noS7R12_Law1934, noS7R12_Law1949, noS7R12_Law1958, noS7R12_Law1975⟩
