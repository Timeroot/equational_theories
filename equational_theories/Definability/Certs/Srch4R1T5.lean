import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 6 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `11`
equations here, 3,379 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1797 takes them (303 nodes). -/
def ordS4R1_Law1797 : List (Fin 8) := [3, 1, 0, 5, 2, 4, 7, 6]

/-- No member of the class satisfies equation 1797. -/
theorem noS4R1_Law1797 : ∀ v : Magma.tup4R1,
    ¬ @Equation1797 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1797) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1797) (by native_decide) v.1 v.2
    ((@Law1797.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1816 takes them (185 nodes). -/
def ordS4R1_Law1816 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1816. -/
theorem noS4R1_Law1816 : ∀ v : Magma.tup4R1,
    ¬ @Equation1816 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1816) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law1816) (by native_decide) v.1 v.2
    ((@Law1816.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1852 takes them (365 nodes). -/
def ordS4R1_Law1852 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1852. -/
theorem noS4R1_Law1852 : ∀ v : Magma.tup4R1,
    ¬ @Equation1852 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1852) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1852) (by native_decide) v.1 v.2
    ((@Law1852.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1862 takes them (289 nodes). -/
def ordS4R1_Law1862 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1862. -/
theorem noS4R1_Law1862 : ∀ v : Magma.tup4R1,
    ¬ @Equation1862 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1862) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1862) (by native_decide) v.1 v.2
    ((@Law1862.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1872 takes them (352 nodes). -/
def ordS4R1_Law1872 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1872. -/
theorem noS4R1_Law1872 : ∀ v : Magma.tup4R1,
    ¬ @Equation1872 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1872) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1872) (by native_decide) v.1 v.2
    ((@Law1872.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1874 takes them (192 nodes). -/
def ordS4R1_Law1874 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1874. -/
theorem noS4R1_Law1874 : ∀ v : Magma.tup4R1,
    ¬ @Equation1874 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1874) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law1874) (by native_decide) v.1 v.2
    ((@Law1874.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1912 takes them (338 nodes). -/
def ordS4R1_Law1912 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1912. -/
theorem noS4R1_Law1912 : ∀ v : Magma.tup4R1,
    ¬ @Equation1912 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1912) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1912) (by native_decide) v.1 v.2
    ((@Law1912.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1924 takes them (569 nodes). -/
def ordS4R1_Law1924 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1924. -/
theorem noS4R1_Law1924 : ∀ v : Magma.tup4R1,
    ¬ @Equation1924 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1924) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law1924) (by native_decide) v.1 v.2
    ((@Law1924.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1979 takes them (322 nodes). -/
def ordS4R1_Law1979 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1979. -/
theorem noS4R1_Law1979 : ∀ v : Magma.tup4R1,
    ¬ @Equation1979 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1979) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1979) (by native_decide) v.1 v.2
    ((@Law1979.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2000 takes them (279 nodes). -/
def ordS4R1_Law2000 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2000. -/
theorem noS4R1_Law2000 : ∀ v : Magma.tup4R1,
    ¬ @Equation2000 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2000) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2000) (by native_decide) v.1 v.2
    ((@Law2000.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2024 takes them (185 nodes). -/
def ordS4R1_Law2024 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2024. -/
theorem noS4R1_Law2024 : ∀ v : Magma.tup4R1,
    ¬ @Equation2024 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2024) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law2024) (by native_decide) v.1 v.2
    ((@Law2024.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch4R1_refutes_5 :
    FamilyRefutes Magma.srch4R1 [
      1797, 1816, 1852, 1862, 1872, 1874, 1912, 1924, 1979, 2000, 2024
    ] :=
  ⟨noS4R1_Law1797, noS4R1_Law1816, noS4R1_Law1852, noS4R1_Law1862, noS4R1_Law1872, noS4R1_Law1874, noS4R1_Law1912, noS4R1_Law1924, noS4R1_Law1979, noS4R1_Law2000, noS4R1_Law2024⟩
