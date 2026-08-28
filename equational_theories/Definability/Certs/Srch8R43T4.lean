import equational_theories.Definability.Srch_S8R43

/-!
# Structural certificate targets: `Magma.srch8R43` (part 5 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R43_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `11` equations here, 829 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R43_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4518 takes them (76 nodes). -/
def ordS8R43_Law4518 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4518. -/
theorem noS8R43_Law4518 : ∀ v : Magma.tup8R43,
    ¬ @Equation4518 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4518) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4518) (by native_decide) v.1 v.2
    ((@Law4518.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4524 takes them (51 nodes). -/
def ordS8R43_Law4524 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4524. -/
theorem noS8R43_Law4524 : ∀ v : Magma.tup8R43,
    ¬ @Equation4524 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4524) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4524) (by native_decide) v.1 v.2
    ((@Law4524.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4532 takes them (83 nodes). -/
def ordS8R43_Law4532 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4532. -/
theorem noS8R43_Law4532 : ∀ v : Magma.tup8R43,
    ¬ @Equation4532 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4532) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4532) (by native_decide) v.1 v.2
    ((@Law4532.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4536 takes them (43 nodes). -/
def ordS8R43_Law4536 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4536. -/
theorem noS8R43_Law4536 : ∀ v : Magma.tup8R43,
    ¬ @Equation4536 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4536) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4536) (by native_decide) v.1 v.2
    ((@Law4536.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4542 takes them (123 nodes). -/
def ordS8R43_Law4542 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4542. -/
theorem noS8R43_Law4542 : ∀ v : Magma.tup8R43,
    ¬ @Equation4542 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4542) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4542) (by native_decide) v.1 v.2
    ((@Law4542.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4546 takes them (158 nodes). -/
def ordS8R43_Law4546 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4546. -/
theorem noS8R43_Law4546 : ∀ v : Magma.tup8R43,
    ¬ @Equation4546 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4546) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 3)
    (ord := ordS8R43_Law4546) (by native_decide) v.1 v.2
    ((@Law4546.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4554 takes them (105 nodes). -/
def ordS8R43_Law4554 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4554. -/
theorem noS8R43_Law4554 : ∀ v : Magma.tup8R43,
    ¬ @Equation4554 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4554) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4554) (by native_decide) v.1 v.2
    ((@Law4554.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4560 takes them (43 nodes). -/
def ordS8R43_Law4560 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4560. -/
theorem noS8R43_Law4560 : ∀ v : Magma.tup8R43,
    ¬ @Equation4560 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4560) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4560) (by native_decide) v.1 v.2
    ((@Law4560.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4565 takes them (43 nodes). -/
def ordS8R43_Law4565 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4565. -/
theorem noS8R43_Law4565 : ∀ v : Magma.tup8R43,
    ¬ @Equation4565 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4565) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4565) (by native_decide) v.1 v.2
    ((@Law4565.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4570 takes them (61 nodes). -/
def ordS8R43_Law4570 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4570. -/
theorem noS8R43_Law4570 : ∀ v : Magma.tup8R43,
    ¬ @Equation4570 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4570) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 4)
    (ord := ordS8R43_Law4570) (by native_decide) v.1 v.2
    ((@Law4570.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4580 takes them (43 nodes). -/
def ordS8R43_Law4580 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4580. -/
theorem noS8R43_Law4580 : ∀ v : Magma.tup8R43,
    ¬ @Equation4580 (Fin 8) (Magma.srch8R43 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4580) (E := S8R43.E) (tr := S8R43.tr) (z := S8R43.z)
    (st := S8R43.st) (X := S8R43.X) (envs := Magma.envsRed 8 S8R43.E 5)
    (ord := ordS8R43_Law4580) (by native_decide) v.1 v.2
    ((@Law4580.models_iff (Fin 8) (Magma.srch8R43 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch8R43_refutes_4 :
    FamilyRefutes Magma.srch8R43 [
      4518, 4524, 4532, 4536, 4542, 4546, 4554, 4560, 4565, 4570, 4580
    ] :=
  ⟨noS8R43_Law4518, noS8R43_Law4524, noS8R43_Law4532, noS8R43_Law4536, noS8R43_Law4542, noS8R43_Law4546, noS8R43_Law4554, noS8R43_Law4560, noS8R43_Law4565, noS8R43_Law4570, noS8R43_Law4580⟩
