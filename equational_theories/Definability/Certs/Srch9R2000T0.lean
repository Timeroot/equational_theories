import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 1 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 1,997 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4 takes them (15 nodes). -/
def ordS9R2000_Law4 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4. -/
theorem noS9R2000_Law4 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 2)
    (ord := ordS9R2000_Law4) (by native_decide) v.1 v.2
    ((@Law4.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 5 takes them (15 nodes). -/
def ordS9R2000_Law5 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 5. -/
theorem noS9R2000_Law5 : ∀ v : Magma.tup9R2000,
    ¬ @Equation5 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law5) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 2)
    (ord := ordS9R2000_Law5) (by native_decide) v.1 v.2
    ((@Law5.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 12 takes them (59 nodes). -/
def ordS9R2000_Law12 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 12. -/
theorem noS9R2000_Law12 : ∀ v : Magma.tup9R2000,
    ¬ @Equation12 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law12) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law12) (by native_decide) v.1 v.2
    ((@Law12.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 13 takes them (1663 nodes). -/
def ordS9R2000_Law13 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 13. -/
theorem noS9R2000_Law13 : ∀ v : Magma.tup9R2000,
    ¬ @Equation13 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law13) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 2)
    (ord := ordS9R2000_Law13) (by native_decide) v.1 v.2
    ((@Law13.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 19 takes them (54 nodes). -/
def ordS9R2000_Law19 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 19. -/
theorem noS9R2000_Law19 : ∀ v : Magma.tup9R2000,
    ¬ @Equation19 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law19) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law19) (by native_decide) v.1 v.2
    ((@Law19.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 24 takes them (47 nodes). -/
def ordS9R2000_Law24 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 24. -/
theorem noS9R2000_Law24 : ∀ v : Magma.tup9R2000,
    ¬ @Equation24 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law24) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 2)
    (ord := ordS9R2000_Law24) (by native_decide) v.1 v.2
    ((@Law24.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 27 takes them (42 nodes). -/
def ordS9R2000_Law27 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 27. -/
theorem noS9R2000_Law27 : ∀ v : Magma.tup9R2000,
    ¬ @Equation27 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law27) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law27) (by native_decide) v.1 v.2
    ((@Law27.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 34 takes them (15 nodes). -/
def ordS9R2000_Law34 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 34. -/
theorem noS9R2000_Law34 : ∀ v : Magma.tup9R2000,
    ¬ @Equation34 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law34) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law34) (by native_decide) v.1 v.2
    ((@Law34.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 38 takes them (87 nodes). -/
def ordS9R2000_Law38 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 38. -/
theorem noS9R2000_Law38 : ∀ v : Magma.tup9R2000,
    ¬ @Equation38 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law38) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 2)
    (ord := ordS9R2000_Law38) (by native_decide) v.1 v.2
    ((@Law38.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch9R2000_refutes_0 :
    FamilyRefutes Magma.srch9R2000 [
      4, 5, 12, 13, 19, 24, 27, 34, 38
    ] :=
  ⟨noS9R2000_Law4, noS9R2000_Law5, noS9R2000_Law12, noS9R2000_Law13, noS9R2000_Law19, noS9R2000_Law24, noS9R2000_Law27, noS9R2000_Law34, noS9R2000_Law38⟩
