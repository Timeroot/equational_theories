import equational_theories.Definability.Srch_S9R403

/-!
# Structural certificate targets: `Magma.srch9R403` (part 1 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R403_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `16` equations here, 3,268 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R403_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 16 takes them (125 nodes). -/
def ordS9R403_Law16 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 16. -/
theorem noS9R403_Law16 : ∀ v : Magma.tup9R403,
    ¬ @Equation16 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law16) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law16) (by native_decide) v.1 v.2
    ((@Law16.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 26 takes them (288 nodes). -/
def ordS9R403_Law26 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 26. -/
theorem noS9R403_Law26 : ∀ v : Magma.tup9R403,
    ¬ @Equation26 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law26) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law26) (by native_decide) v.1 v.2
    ((@Law26.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 466 takes them (194 nodes). -/
def ordS9R403_Law466 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 466. -/
theorem noS9R403_Law466 : ∀ v : Magma.tup9R403,
    ¬ @Equation466 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 473 takes them (104 nodes). -/
def ordS9R403_Law473 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 473. -/
theorem noS9R403_Law473 : ∀ v : Magma.tup9R403,
    ¬ @Equation473 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law473) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law473) (by native_decide) v.1 v.2
    ((@Law473.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 500 takes them (212 nodes). -/
def ordS9R403_Law500 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 500. -/
theorem noS9R403_Law500 : ∀ v : Magma.tup9R403,
    ¬ @Equation500 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law500) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law500) (by native_decide) v.1 v.2
    ((@Law500.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 513 takes them (127 nodes). -/
def ordS9R403_Law513 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 513. -/
theorem noS9R403_Law513 : ∀ v : Magma.tup9R403,
    ¬ @Equation513 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law513) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law513) (by native_decide) v.1 v.2
    ((@Law513.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 528 takes them (127 nodes). -/
def ordS9R403_Law528 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 528. -/
theorem noS9R403_Law528 : ∀ v : Magma.tup9R403,
    ¬ @Equation528 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law528) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law528) (by native_decide) v.1 v.2
    ((@Law528.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 575 takes them (127 nodes). -/
def ordS9R403_Law575 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 575. -/
theorem noS9R403_Law575 : ∀ v : Magma.tup9R403,
    ¬ @Equation575 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law575) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law575) (by native_decide) v.1 v.2
    ((@Law575.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 703 takes them (304 nodes). -/
def ordS9R403_Law703 : List (Fin 7) := [6, 2, 1, 3, 5, 0, 4]

/-- No member of the class satisfies equation 703. -/
theorem noS9R403_Law703 : ∀ v : Magma.tup9R403,
    ¬ @Equation703 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law703) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law703) (by native_decide) v.1 v.2
    ((@Law703.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (394 nodes). -/
def ordS9R403_Law1075 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1075. -/
theorem noS9R403_Law1075 : ∀ v : Magma.tup9R403,
    ¬ @Equation1075 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (228 nodes). -/
def ordS9R403_Law1122 : List (Fin 7) := [6, 5, 2, 4, 0, 1, 3]

/-- No member of the class satisfies equation 1122. -/
theorem noS9R403_Law1122 : ∀ v : Magma.tup9R403,
    ¬ @Equation1122 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (186 nodes). -/
def ordS9R403_Law1184 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1184. -/
theorem noS9R403_Law1184 : ∀ v : Magma.tup9R403,
    ¬ @Equation1184 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1278 takes them (209 nodes). -/
def ordS9R403_Law1278 : List (Fin 7) := [6, 0, 5, 2, 4, 3, 1]

/-- No member of the class satisfies equation 1278. -/
theorem noS9R403_Law1278 : ∀ v : Magma.tup9R403,
    ¬ @Equation1278 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1278) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1278) (by native_decide) v.1 v.2
    ((@Law1278.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1325 takes them (242 nodes). -/
def ordS9R403_Law1325 : List (Fin 7) := [0, 3, 6, 5, 1, 2, 4]

/-- No member of the class satisfies equation 1325. -/
theorem noS9R403_Law1325 : ∀ v : Magma.tup9R403,
    ¬ @Equation1325 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1325) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1325) (by native_decide) v.1 v.2
    ((@Law1325.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1455 takes them (275 nodes). -/
def ordS9R403_Law1455 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 1455. -/
theorem noS9R403_Law1455 : ∀ v : Magma.tup9R403,
    ¬ @Equation1455 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1455) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1455) (by native_decide) v.1 v.2
    ((@Law1455.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1645 takes them (126 nodes). -/
def ordS9R403_Law1645 : List (Fin 7) := [2, 6, 3, 0, 5, 4, 1]

/-- No member of the class satisfies equation 1645. -/
theorem noS9R403_Law1645 : ∀ v : Magma.tup9R403,
    ¬ @Equation1645 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1645) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law1645) (by native_decide) v.1 v.2
    ((@Law1645.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch9R403_refutes_0 :
    FamilyRefutes Magma.srch9R403 [
      16, 26, 466, 473, 500, 513, 528, 575, 703, 1075, 1122, 1184, 1278, 1325, 1455, 1645
    ] :=
  ⟨noS9R403_Law16, noS9R403_Law26, noS9R403_Law466, noS9R403_Law473, noS9R403_Law500, noS9R403_Law513, noS9R403_Law528, noS9R403_Law575, noS9R403_Law703, noS9R403_Law1075, noS9R403_Law1122, noS9R403_Law1184, noS9R403_Law1278, noS9R403_Law1325, noS9R403_Law1455, noS9R403_Law1645⟩
