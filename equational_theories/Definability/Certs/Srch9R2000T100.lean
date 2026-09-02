import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 101 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `5` equations here, 1,888 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1878 takes them (126 nodes). -/
def ordS9R2000_Law1878 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 1878. -/
theorem noS9R2000_Law1878 : ∀ v : Magma.tup9R2000,
    ¬ @Equation1878 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1878) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law1878) (by native_decide) v.1 v.2
    ((@Law1878.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1880 takes them (622 nodes). -/
def ordS9R2000_Law1880 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 1880. -/
theorem noS9R2000_Law1880 : ∀ v : Magma.tup9R2000,
    ¬ @Equation1880 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1880) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law1880) (by native_decide) v.1 v.2
    ((@Law1880.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1881 takes them (524 nodes). -/
def ordS9R2000_Law1881 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 1881. -/
theorem noS9R2000_Law1881 : ∀ v : Magma.tup9R2000,
    ¬ @Equation1881 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1881) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law1881) (by native_decide) v.1 v.2
    ((@Law1881.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1882 takes them (530 nodes). -/
def ordS9R2000_Law1882 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 1882. -/
theorem noS9R2000_Law1882 : ∀ v : Magma.tup9R2000,
    ¬ @Equation1882 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1882) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law1882) (by native_decide) v.1 v.2
    ((@Law1882.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1883 takes them (86 nodes). -/
def ordS9R2000_Law1883 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 1883. -/
theorem noS9R2000_Law1883 : ∀ v : Magma.tup9R2000,
    ¬ @Equation1883 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1883) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 5)
    (ord := ordS9R2000_Law1883) (by native_decide) v.1 v.2
    ((@Law1883.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch9R2000_refutes_100 :
    FamilyRefutes Magma.srch9R2000 [
      1878, 1880, 1881, 1882, 1883
    ] :=
  ⟨noS9R2000_Law1878, noS9R2000_Law1880, noS9R2000_Law1881, noS9R2000_Law1882, noS9R2000_Law1883⟩
