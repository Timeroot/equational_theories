import equational_theories.Definability.Srch_S9R205

/-!
# Structural certificate targets: `Magma.srch9R205` (part 3 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R205_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `67` equations here, 256 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R205_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3306 takes them (5 nodes). -/
def ordS9R205_Law3306 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3306. -/
theorem noS9R205_Law3306 : ∀ v : Magma.tup9R205,
    ¬ @Equation3306 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3306) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3306) (by native_decide) v.1 v.2
    ((@Law3306.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (4 nodes). -/
def ordS9R205_Law3308 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3308. -/
theorem noS9R205_Law3308 : ∀ v : Magma.tup9R205,
    ¬ @Equation3308 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (4 nodes). -/
def ordS9R205_Law3331 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3331. -/
theorem noS9R205_Law3331 : ∀ v : Magma.tup9R205,
    ¬ @Equation3331 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (5 nodes). -/
def ordS9R205_Law3334 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3334. -/
theorem noS9R205_Law3334 : ∀ v : Magma.tup9R205,
    ¬ @Equation3334 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3343 takes them (3 nodes). -/
def ordS9R205_Law3343 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3343. -/
theorem noS9R205_Law3343 : ∀ v : Magma.tup9R205,
    ¬ @Equation3343 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3343) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3343) (by native_decide) v.1 v.2
    ((@Law3343.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3353 takes them (4 nodes). -/
def ordS9R205_Law3353 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3353. -/
theorem noS9R205_Law3353 : ∀ v : Magma.tup9R205,
    ¬ @Equation3353 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3353) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3353) (by native_decide) v.1 v.2
    ((@Law3353.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (4 nodes). -/
def ordS9R205_Law3414 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3414. -/
theorem noS9R205_Law3414 : ∀ v : Magma.tup9R205,
    ¬ @Equation3414 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3459 takes them (4 nodes). -/
def ordS9R205_Law3459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3459. -/
theorem noS9R205_Law3459 : ∀ v : Magma.tup9R205,
    ¬ @Equation3459 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3459) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3459) (by native_decide) v.1 v.2
    ((@Law3459.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3462 takes them (4 nodes). -/
def ordS9R205_Law3462 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3462. -/
theorem noS9R205_Law3462 : ∀ v : Magma.tup9R205,
    ¬ @Equation3462 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3462) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3462) (by native_decide) v.1 v.2
    ((@Law3462.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3472 takes them (3 nodes). -/
def ordS9R205_Law3472 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3472. -/
theorem noS9R205_Law3472 : ∀ v : Magma.tup9R205,
    ¬ @Equation3472 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3472) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3472) (by native_decide) v.1 v.2
    ((@Law3472.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3481 takes them (3 nodes). -/
def ordS9R205_Law3481 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3481. -/
theorem noS9R205_Law3481 : ∀ v : Magma.tup9R205,
    ¬ @Equation3481 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3481) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3481) (by native_decide) v.1 v.2
    ((@Law3481.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3484 takes them (4 nodes). -/
def ordS9R205_Law3484 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3484. -/
theorem noS9R205_Law3484 : ∀ v : Magma.tup9R205,
    ¬ @Equation3484 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3484) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3484) (by native_decide) v.1 v.2
    ((@Law3484.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3511 takes them (4 nodes). -/
def ordS9R205_Law3511 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3511. -/
theorem noS9R205_Law3511 : ∀ v : Magma.tup9R205,
    ¬ @Equation3511 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3511) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3511) (by native_decide) v.1 v.2
    ((@Law3511.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3518 takes them (4 nodes). -/
def ordS9R205_Law3518 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3518. -/
theorem noS9R205_Law3518 : ∀ v : Magma.tup9R205,
    ¬ @Equation3518 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3518) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3518) (by native_decide) v.1 v.2
    ((@Law3518.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (4 nodes). -/
def ordS9R205_Law3526 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3526. -/
theorem noS9R205_Law3526 : ∀ v : Magma.tup9R205,
    ¬ @Equation3526 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (4 nodes). -/
def ordS9R205_Law3534 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3534. -/
theorem noS9R205_Law3534 : ∀ v : Magma.tup9R205,
    ¬ @Equation3534 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3549 takes them (4 nodes). -/
def ordS9R205_Law3549 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3549. -/
theorem noS9R205_Law3549 : ∀ v : Magma.tup9R205,
    ¬ @Equation3549 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3667 takes them (4 nodes). -/
def ordS9R205_Law3667 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3667. -/
theorem noS9R205_Law3667 : ∀ v : Magma.tup9R205,
    ¬ @Equation3667 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3667) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3667) (by native_decide) v.1 v.2
    ((@Law3667.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3668 takes them (4 nodes). -/
def ordS9R205_Law3668 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3668. -/
theorem noS9R205_Law3668 : ∀ v : Magma.tup9R205,
    ¬ @Equation3668 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3668) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3668) (by native_decide) v.1 v.2
    ((@Law3668.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3687 takes them (4 nodes). -/
def ordS9R205_Law3687 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3687. -/
theorem noS9R205_Law3687 : ∀ v : Magma.tup9R205,
    ¬ @Equation3687 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3687) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3687) (by native_decide) v.1 v.2
    ((@Law3687.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3724 takes them (4 nodes). -/
def ordS9R205_Law3724 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3724. -/
theorem noS9R205_Law3724 : ∀ v : Magma.tup9R205,
    ¬ @Equation3724 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3724) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3724) (by native_decide) v.1 v.2
    ((@Law3724.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3749 takes them (4 nodes). -/
def ordS9R205_Law3749 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3749. -/
theorem noS9R205_Law3749 : ∀ v : Magma.tup9R205,
    ¬ @Equation3749 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3749) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3749) (by native_decide) v.1 v.2
    ((@Law3749.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3865 takes them (3 nodes). -/
def ordS9R205_Law3865 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3865. -/
theorem noS9R205_Law3865 : ∀ v : Magma.tup9R205,
    ¬ @Equation3865 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3865) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3865) (by native_decide) v.1 v.2
    ((@Law3865.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3871 takes them (4 nodes). -/
def ordS9R205_Law3871 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3871. -/
theorem noS9R205_Law3871 : ∀ v : Magma.tup9R205,
    ¬ @Equation3871 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3871) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3871) (by native_decide) v.1 v.2
    ((@Law3871.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3878 takes them (3 nodes). -/
def ordS9R205_Law3878 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3878. -/
theorem noS9R205_Law3878 : ∀ v : Magma.tup9R205,
    ¬ @Equation3878 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3878) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3878) (by native_decide) v.1 v.2
    ((@Law3878.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3880 takes them (4 nodes). -/
def ordS9R205_Law3880 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3880. -/
theorem noS9R205_Law3880 : ∀ v : Magma.tup9R205,
    ¬ @Equation3880 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3880) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3880) (by native_decide) v.1 v.2
    ((@Law3880.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3887 takes them (4 nodes). -/
def ordS9R205_Law3887 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3887. -/
theorem noS9R205_Law3887 : ∀ v : Magma.tup9R205,
    ¬ @Equation3887 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3887) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3887) (by native_decide) v.1 v.2
    ((@Law3887.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3917 takes them (4 nodes). -/
def ordS9R205_Law3917 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3917. -/
theorem noS9R205_Law3917 : ∀ v : Magma.tup9R205,
    ¬ @Equation3917 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3917) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3917) (by native_decide) v.1 v.2
    ((@Law3917.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3955 takes them (4 nodes). -/
def ordS9R205_Law3955 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3955. -/
theorem noS9R205_Law3955 : ∀ v : Magma.tup9R205,
    ¬ @Equation3955 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3955) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3955) (by native_decide) v.1 v.2
    ((@Law3955.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3962 takes them (4 nodes). -/
def ordS9R205_Law3962 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3962. -/
theorem noS9R205_Law3962 : ∀ v : Magma.tup9R205,
    ¬ @Equation3962 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3962) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law3962) (by native_decide) v.1 v.2
    ((@Law3962.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3997 takes them (4 nodes). -/
def ordS9R205_Law3997 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3997. -/
theorem noS9R205_Law3997 : ∀ v : Magma.tup9R205,
    ¬ @Equation3997 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (4 nodes). -/
def ordS9R205_Law4023 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4023. -/
theorem noS9R205_Law4023 : ∀ v : Magma.tup9R205,
    ¬ @Equation4023 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4068 takes them (4 nodes). -/
def ordS9R205_Law4068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4068. -/
theorem noS9R205_Law4068 : ∀ v : Magma.tup9R205,
    ¬ @Equation4068 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4068) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4068) (by native_decide) v.1 v.2
    ((@Law4068.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4073 takes them (5 nodes). -/
def ordS9R205_Law4073 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4073. -/
theorem noS9R205_Law4073 : ∀ v : Magma.tup9R205,
    ¬ @Equation4073 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4073) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4073) (by native_decide) v.1 v.2
    ((@Law4073.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4074 takes them (3 nodes). -/
def ordS9R205_Law4074 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4074. -/
theorem noS9R205_Law4074 : ∀ v : Magma.tup9R205,
    ¬ @Equation4074 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4074) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4074) (by native_decide) v.1 v.2
    ((@Law4074.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4083 takes them (4 nodes). -/
def ordS9R205_Law4083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4083. -/
theorem noS9R205_Law4083 : ∀ v : Magma.tup9R205,
    ¬ @Equation4083 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4083) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4083) (by native_decide) v.1 v.2
    ((@Law4083.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4091 takes them (3 nodes). -/
def ordS9R205_Law4091 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4091. -/
theorem noS9R205_Law4091 : ∀ v : Magma.tup9R205,
    ¬ @Equation4091 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4091) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4091) (by native_decide) v.1 v.2
    ((@Law4091.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4127 takes them (4 nodes). -/
def ordS9R205_Law4127 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4127. -/
theorem noS9R205_Law4127 : ∀ v : Magma.tup9R205,
    ¬ @Equation4127 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4127) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4127) (by native_decide) v.1 v.2
    ((@Law4127.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4130 takes them (3 nodes). -/
def ordS9R205_Law4130 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4130. -/
theorem noS9R205_Law4130 : ∀ v : Magma.tup9R205,
    ¬ @Equation4130 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4130) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4130) (by native_decide) v.1 v.2
    ((@Law4130.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4131 takes them (5 nodes). -/
def ordS9R205_Law4131 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4131. -/
theorem noS9R205_Law4131 : ∀ v : Magma.tup9R205,
    ¬ @Equation4131 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4131) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4131) (by native_decide) v.1 v.2
    ((@Law4131.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (4 nodes). -/
def ordS9R205_Law4135 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4135. -/
theorem noS9R205_Law4135 : ∀ v : Magma.tup9R205,
    ¬ @Equation4135 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (5 nodes). -/
def ordS9R205_Law4146 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4146. -/
theorem noS9R205_Law4146 : ∀ v : Magma.tup9R205,
    ¬ @Equation4146 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4158 takes them (4 nodes). -/
def ordS9R205_Law4158 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4158. -/
theorem noS9R205_Law4158 : ∀ v : Magma.tup9R205,
    ¬ @Equation4158 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (4 nodes). -/
def ordS9R205_Law4200 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4200. -/
theorem noS9R205_Law4200 : ∀ v : Magma.tup9R205,
    ¬ @Equation4200 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4273 takes them (3 nodes). -/
def ordS9R205_Law4273 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4273. -/
theorem noS9R205_Law4273 : ∀ v : Magma.tup9R205,
    ¬ @Equation4273 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4273) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4273) (by native_decide) v.1 v.2
    ((@Law4273.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4275 takes them (4 nodes). -/
def ordS9R205_Law4275 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4275. -/
theorem noS9R205_Law4275 : ∀ v : Magma.tup9R205,
    ¬ @Equation4275 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (4 nodes). -/
def ordS9R205_Law4283 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4283. -/
theorem noS9R205_Law4283 : ∀ v : Magma.tup9R205,
    ¬ @Equation4283 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4307 takes them (4 nodes). -/
def ordS9R205_Law4307 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4307. -/
theorem noS9R205_Law4307 : ∀ v : Magma.tup9R205,
    ¬ @Equation4307 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4332 takes them (3 nodes). -/
def ordS9R205_Law4332 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4332. -/
theorem noS9R205_Law4332 : ∀ v : Magma.tup9R205,
    ¬ @Equation4332 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4332) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4332) (by native_decide) v.1 v.2
    ((@Law4332.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4343 takes them (3 nodes). -/
def ordS9R205_Law4343 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4343. -/
theorem noS9R205_Law4343 : ∀ v : Magma.tup9R205,
    ¬ @Equation4343 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4343) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4343) (by native_decide) v.1 v.2
    ((@Law4343.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4358 takes them (4 nodes). -/
def ordS9R205_Law4358 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4358. -/
theorem noS9R205_Law4358 : ∀ v : Magma.tup9R205,
    ¬ @Equation4358 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4383 takes them (4 nodes). -/
def ordS9R205_Law4383 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4383. -/
theorem noS9R205_Law4383 : ∀ v : Magma.tup9R205,
    ¬ @Equation4383 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4383) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4383) (by native_decide) v.1 v.2
    ((@Law4383.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4386 takes them (3 nodes). -/
def ordS9R205_Law4386 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4386. -/
theorem noS9R205_Law4386 : ∀ v : Magma.tup9R205,
    ¬ @Equation4386 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4386) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4386) (by native_decide) v.1 v.2
    ((@Law4386.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4398 takes them (4 nodes). -/
def ordS9R205_Law4398 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4398. -/
theorem noS9R205_Law4398 : ∀ v : Magma.tup9R205,
    ¬ @Equation4398 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4398) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4398) (by native_decide) v.1 v.2
    ((@Law4398.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4409 takes them (4 nodes). -/
def ordS9R205_Law4409 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4409. -/
theorem noS9R205_Law4409 : ∀ v : Magma.tup9R205,
    ¬ @Equation4409 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4409) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4409) (by native_decide) v.1 v.2
    ((@Law4409.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4435 takes them (5 nodes). -/
def ordS9R205_Law4435 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4435. -/
theorem noS9R205_Law4435 : ∀ v : Magma.tup9R205,
    ¬ @Equation4435 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4435) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4435) (by native_decide) v.1 v.2
    ((@Law4435.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4442 takes them (4 nodes). -/
def ordS9R205_Law4442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4442. -/
theorem noS9R205_Law4442 : ∀ v : Magma.tup9R205,
    ¬ @Equation4442 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4442) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4442) (by native_decide) v.1 v.2
    ((@Law4442.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4446 takes them (3 nodes). -/
def ordS9R205_Law4446 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4446. -/
theorem noS9R205_Law4446 : ∀ v : Magma.tup9R205,
    ¬ @Equation4446 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4446) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4446) (by native_decide) v.1 v.2
    ((@Law4446.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4458 takes them (3 nodes). -/
def ordS9R205_Law4458 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4458. -/
theorem noS9R205_Law4458 : ∀ v : Magma.tup9R205,
    ¬ @Equation4458 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4458) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4458) (by native_decide) v.1 v.2
    ((@Law4458.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4482 takes them (3 nodes). -/
def ordS9R205_Law4482 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4482. -/
theorem noS9R205_Law4482 : ∀ v : Magma.tup9R205,
    ¬ @Equation4482 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4482) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4482) (by native_decide) v.1 v.2
    ((@Law4482.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4585 takes them (4 nodes). -/
def ordS9R205_Law4585 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4585. -/
theorem noS9R205_Law4585 : ∀ v : Magma.tup9R205,
    ¬ @Equation4585 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4585) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4585) (by native_decide) v.1 v.2
    ((@Law4585.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4588 takes them (3 nodes). -/
def ordS9R205_Law4588 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4588. -/
theorem noS9R205_Law4588 : ∀ v : Magma.tup9R205,
    ¬ @Equation4588 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4588) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4588) (by native_decide) v.1 v.2
    ((@Law4588.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4608 takes them (3 nodes). -/
def ordS9R205_Law4608 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4608. -/
theorem noS9R205_Law4608 : ∀ v : Magma.tup9R205,
    ¬ @Equation4608 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4608) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4608) (by native_decide) v.1 v.2
    ((@Law4608.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (4 nodes). -/
def ordS9R205_Law4635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4635. -/
theorem noS9R205_Law4635 : ∀ v : Magma.tup9R205,
    ¬ @Equation4635 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 2)
    (ord := ordS9R205_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4647 takes them (3 nodes). -/
def ordS9R205_Law4647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4647. -/
theorem noS9R205_Law4647 : ∀ v : Magma.tup9R205,
    ¬ @Equation4647 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4647) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4647) (by native_decide) v.1 v.2
    ((@Law4647.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4656 takes them (4 nodes). -/
def ordS9R205_Law4656 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4656. -/
theorem noS9R205_Law4656 : ∀ v : Magma.tup9R205,
    ¬ @Equation4656 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4656) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4656) (by native_decide) v.1 v.2
    ((@Law4656.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4677 takes them (4 nodes). -/
def ordS9R205_Law4677 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4677. -/
theorem noS9R205_Law4677 : ∀ v : Magma.tup9R205,
    ¬ @Equation4677 (Fin 9) (Magma.srch9R205 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4677) (E := S9R205.E) (tr := S9R205.tr) (z := S9R205.z)
    (st := S9R205.st) (X := S9R205.X) (envs := Magma.envsRed 9 S9R205.E 3)
    (ord := ordS9R205_Law4677) (by native_decide) v.1 v.2
    ((@Law4677.models_iff (Fin 9) (Magma.srch9R205 v)).mpr hv)

/-- No member of the class satisfies any of these `67` equations. -/
theorem srch9R205_refutes_2 :
    FamilyRefutes Magma.srch9R205 [
      3306, 3308, 3331, 3334, 3343, 3353, 3414, 3459, 3462, 3472, 3481, 3484, 3511, 3518, 3526,
      3534, 3549, 3667, 3668, 3687, 3724, 3749, 3865, 3871, 3878, 3880, 3887, 3917, 3955, 3962,
      3997, 4023, 4068, 4073, 4074, 4083, 4091, 4127, 4130, 4131, 4135, 4146, 4158, 4200, 4273,
      4275, 4283, 4307, 4332, 4343, 4358, 4383, 4386, 4398, 4409, 4435, 4442, 4446, 4458, 4482,
      4585, 4588, 4608, 4635, 4647, 4656, 4677
    ] :=
  ⟨noS9R205_Law3306, noS9R205_Law3308, noS9R205_Law3331, noS9R205_Law3334, noS9R205_Law3343, noS9R205_Law3353, noS9R205_Law3414, noS9R205_Law3459, noS9R205_Law3462, noS9R205_Law3472, noS9R205_Law3481, noS9R205_Law3484, noS9R205_Law3511, noS9R205_Law3518, noS9R205_Law3526, noS9R205_Law3534, noS9R205_Law3549, noS9R205_Law3667, noS9R205_Law3668, noS9R205_Law3687, noS9R205_Law3724, noS9R205_Law3749, noS9R205_Law3865, noS9R205_Law3871, noS9R205_Law3878, noS9R205_Law3880, noS9R205_Law3887, noS9R205_Law3917, noS9R205_Law3955, noS9R205_Law3962, noS9R205_Law3997, noS9R205_Law4023, noS9R205_Law4068, noS9R205_Law4073, noS9R205_Law4074, noS9R205_Law4083, noS9R205_Law4091, noS9R205_Law4127, noS9R205_Law4130, noS9R205_Law4131, noS9R205_Law4135, noS9R205_Law4146, noS9R205_Law4158, noS9R205_Law4200, noS9R205_Law4273, noS9R205_Law4275, noS9R205_Law4283, noS9R205_Law4307, noS9R205_Law4332, noS9R205_Law4343, noS9R205_Law4358, noS9R205_Law4383, noS9R205_Law4386, noS9R205_Law4398, noS9R205_Law4409, noS9R205_Law4435, noS9R205_Law4442, noS9R205_Law4446, noS9R205_Law4458, noS9R205_Law4482, noS9R205_Law4585, noS9R205_Law4588, noS9R205_Law4608, noS9R205_Law4635, noS9R205_Law4647, noS9R205_Law4656, noS9R205_Law4677⟩
