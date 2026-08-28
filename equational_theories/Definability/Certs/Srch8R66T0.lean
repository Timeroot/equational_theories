import equational_theories.Definability.Srch_S8R66

/-!
# Structural certificate targets: `Magma.srch8R66` (part 1 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R66_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `14` equations here, 3,409 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R66_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 16 takes them (198 nodes). -/
def ordS8R66_Law16 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 16. -/
theorem noS8R66_Law16 : ∀ v : Magma.tup8R66,
    ¬ @Equation16 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law16) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law16) (by native_decide) v.1 v.2
    ((@Law16.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 26 takes them (299 nodes). -/
def ordS8R66_Law26 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 26. -/
theorem noS8R66_Law26 : ∀ v : Magma.tup8R66,
    ¬ @Equation26 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law26) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law26) (by native_decide) v.1 v.2
    ((@Law26.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 466 takes them (341 nodes). -/
def ordS8R66_Law466 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 466. -/
theorem noS8R66_Law466 : ∀ v : Magma.tup8R66,
    ¬ @Equation466 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law466) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law466) (by native_decide) v.1 v.2
    ((@Law466.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 500 takes them (741 nodes). -/
def ordS8R66_Law500 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 500. -/
theorem noS8R66_Law500 : ∀ v : Magma.tup8R66,
    ¬ @Equation500 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law500) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law500) (by native_decide) v.1 v.2
    ((@Law500.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 513 takes them (274 nodes). -/
def ordS8R66_Law513 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 513. -/
theorem noS8R66_Law513 : ∀ v : Magma.tup8R66,
    ¬ @Equation513 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law513) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law513) (by native_decide) v.1 v.2
    ((@Law513.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 528 takes them (198 nodes). -/
def ordS8R66_Law528 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 528. -/
theorem noS8R66_Law528 : ∀ v : Magma.tup8R66,
    ¬ @Equation528 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law528) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law528) (by native_decide) v.1 v.2
    ((@Law528.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 575 takes them (198 nodes). -/
def ordS8R66_Law575 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 575. -/
theorem noS8R66_Law575 : ∀ v : Magma.tup8R66,
    ¬ @Equation575 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law575) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law575) (by native_decide) v.1 v.2
    ((@Law575.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 703 takes them (481 nodes). -/
def ordS8R66_Law703 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 703. -/
theorem noS8R66_Law703 : ∀ v : Magma.tup8R66,
    ¬ @Equation703 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law703) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law703) (by native_decide) v.1 v.2
    ((@Law703.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 716 takes them (53 nodes). -/
def ordS8R66_Law716 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 716. -/
theorem noS8R66_Law716 : ∀ v : Magma.tup8R66,
    ¬ @Equation716 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law716) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law716) (by native_decide) v.1 v.2
    ((@Law716.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 731 takes them (45 nodes). -/
def ordS8R66_Law731 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 731. -/
theorem noS8R66_Law731 : ∀ v : Magma.tup8R66,
    ¬ @Equation731 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law731) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law731) (by native_decide) v.1 v.2
    ((@Law731.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 872 takes them (229 nodes). -/
def ordS8R66_Law872 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 872. -/
theorem noS8R66_Law872 : ∀ v : Magma.tup8R66,
    ¬ @Equation872 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law872) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law872) (by native_decide) v.1 v.2
    ((@Law872.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 906 takes them (257 nodes). -/
def ordS8R66_Law906 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 906. -/
theorem noS8R66_Law906 : ∀ v : Magma.tup8R66,
    ¬ @Equation906 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law906) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law906) (by native_decide) v.1 v.2
    ((@Law906.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 919 takes them (50 nodes). -/
def ordS8R66_Law919 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 919. -/
theorem noS8R66_Law919 : ∀ v : Magma.tup8R66,
    ¬ @Equation919 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law919) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law919) (by native_decide) v.1 v.2
    ((@Law919.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 981 takes them (45 nodes). -/
def ordS8R66_Law981 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 981. -/
theorem noS8R66_Law981 : ∀ v : Magma.tup8R66,
    ¬ @Equation981 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law981) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law981) (by native_decide) v.1 v.2
    ((@Law981.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch8R66_refutes_0 :
    FamilyRefutes Magma.srch8R66 [
      16, 26, 466, 500, 513, 528, 575, 703, 716, 731, 872, 906, 919, 981
    ] :=
  ⟨noS8R66_Law16, noS8R66_Law26, noS8R66_Law466, noS8R66_Law500, noS8R66_Law513, noS8R66_Law528, noS8R66_Law575, noS8R66_Law703, noS8R66_Law716, noS8R66_Law731, noS8R66_Law872, noS8R66_Law906, noS8R66_Law919, noS8R66_Law981⟩
