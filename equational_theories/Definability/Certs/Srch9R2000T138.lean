import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 139 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 2,270 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2288 takes them (2153 nodes). -/
def ordS9R2000_Law2288 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2288. -/
theorem noS9R2000_Law2288 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2288 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2288) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2288) (by native_decide) v.1 v.2
    ((@Law2288.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2289 takes them (42 nodes). -/
def ordS9R2000_Law2289 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2289. -/
theorem noS9R2000_Law2289 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2289 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2289) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 5)
    (ord := ordS9R2000_Law2289) (by native_decide) v.1 v.2
    ((@Law2289.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2343 takes them (15 nodes). -/
def ordS9R2000_Law2343 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2343. -/
theorem noS9R2000_Law2343 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2343 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2343) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law2343) (by native_decide) v.1 v.2
    ((@Law2343.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2359 takes them (15 nodes). -/
def ordS9R2000_Law2359 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2359. -/
theorem noS9R2000_Law2359 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2359 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2359) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2359) (by native_decide) v.1 v.2
    ((@Law2359.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2393 takes them (15 nodes). -/
def ordS9R2000_Law2393 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2393. -/
theorem noS9R2000_Law2393 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2393 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2393) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2393) (by native_decide) v.1 v.2
    ((@Law2393.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2410 takes them (15 nodes). -/
def ordS9R2000_Law2410 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2410. -/
theorem noS9R2000_Law2410 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2410 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2410) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law2410) (by native_decide) v.1 v.2
    ((@Law2410.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2435 takes them (15 nodes). -/
def ordS9R2000_Law2435 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 2435. -/
theorem noS9R2000_Law2435 : ∀ v : Magma.tup9R2000,
    ¬ @Equation2435 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2435) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 5)
    (ord := ordS9R2000_Law2435) (by native_decide) v.1 v.2
    ((@Law2435.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch9R2000_refutes_138 :
    FamilyRefutes Magma.srch9R2000 [
      2288, 2289, 2343, 2359, 2393, 2410, 2435
    ] :=
  ⟨noS9R2000_Law2288, noS9R2000_Law2289, noS9R2000_Law2343, noS9R2000_Law2359, noS9R2000_Law2393, noS9R2000_Law2410, noS9R2000_Law2435⟩
