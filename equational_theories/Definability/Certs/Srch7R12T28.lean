import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 29 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `15` equations here, 3,299 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2675 takes them (181 nodes). -/
def ordS7R12_Law2675 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2675. -/
theorem noS7R12_Law2675 : ∀ v : Magma.tup7R12,
    ¬ @Equation2675 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2675) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2675) (by native_decide) v.1 v.2
    ((@Law2675.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2679 takes them (199 nodes). -/
def ordS7R12_Law2679 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2679. -/
theorem noS7R12_Law2679 : ∀ v : Magma.tup7R12,
    ¬ @Equation2679 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2679) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2679) (by native_decide) v.1 v.2
    ((@Law2679.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2683 takes them (211 nodes). -/
def ordS7R12_Law2683 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2683. -/
theorem noS7R12_Law2683 : ∀ v : Magma.tup7R12,
    ¬ @Equation2683 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2683) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2683) (by native_decide) v.1 v.2
    ((@Law2683.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2688 takes them (321 nodes). -/
def ordS7R12_Law2688 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2688. -/
theorem noS7R12_Law2688 : ∀ v : Magma.tup7R12,
    ¬ @Equation2688 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2688) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2688) (by native_decide) v.1 v.2
    ((@Law2688.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2691 takes them (121 nodes). -/
def ordS7R12_Law2691 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2691. -/
theorem noS7R12_Law2691 : ∀ v : Magma.tup7R12,
    ¬ @Equation2691 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2691) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2691) (by native_decide) v.1 v.2
    ((@Law2691.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2699 takes them (439 nodes). -/
def ordS7R12_Law2699 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2699. -/
theorem noS7R12_Law2699 : ∀ v : Magma.tup7R12,
    ¬ @Equation2699 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2699) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2699) (by native_decide) v.1 v.2
    ((@Law2699.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2702 takes them (86 nodes). -/
def ordS7R12_Law2702 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2702. -/
theorem noS7R12_Law2702 : ∀ v : Magma.tup7R12,
    ¬ @Equation2702 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2702) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2702) (by native_decide) v.1 v.2
    ((@Law2702.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2712 takes them (86 nodes). -/
def ordS7R12_Law2712 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2712. -/
theorem noS7R12_Law2712 : ∀ v : Magma.tup7R12,
    ¬ @Equation2712 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2712) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2712) (by native_decide) v.1 v.2
    ((@Law2712.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2716 takes them (118 nodes). -/
def ordS7R12_Law2716 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2716. -/
theorem noS7R12_Law2716 : ∀ v : Magma.tup7R12,
    ¬ @Equation2716 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2716) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2716) (by native_decide) v.1 v.2
    ((@Law2716.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2753 takes them (578 nodes). -/
def ordS7R12_Law2753 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2753. -/
theorem noS7R12_Law2753 : ∀ v : Magma.tup7R12,
    ¬ @Equation2753 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2753) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2753) (by native_decide) v.1 v.2
    ((@Law2753.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2774 takes them (126 nodes). -/
def ordS7R12_Law2774 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2774. -/
theorem noS7R12_Law2774 : ∀ v : Magma.tup7R12,
    ¬ @Equation2774 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2774) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2774) (by native_decide) v.1 v.2
    ((@Law2774.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2804 takes them (81 nodes). -/
def ordS7R12_Law2804 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2804. -/
theorem noS7R12_Law2804 : ∀ v : Magma.tup7R12,
    ¬ @Equation2804 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2804) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2804) (by native_decide) v.1 v.2
    ((@Law2804.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2808 takes them (139 nodes). -/
def ordS7R12_Law2808 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2808. -/
theorem noS7R12_Law2808 : ∀ v : Magma.tup7R12,
    ¬ @Equation2808 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2808) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2808) (by native_decide) v.1 v.2
    ((@Law2808.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2821 takes them (66 nodes). -/
def ordS7R12_Law2821 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2821. -/
theorem noS7R12_Law2821 : ∀ v : Magma.tup7R12,
    ¬ @Equation2821 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2821) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2821) (by native_decide) v.1 v.2
    ((@Law2821.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2849 takes them (547 nodes). -/
def ordS7R12_Law2849 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2849. -/
theorem noS7R12_Law2849 : ∀ v : Magma.tup7R12,
    ¬ @Equation2849 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2849) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2849) (by native_decide) v.1 v.2
    ((@Law2849.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `15` equations. -/
theorem srch7R12_refutes_28 :
    FamilyRefutes Magma.srch7R12 [
      2675, 2679, 2683, 2688, 2691, 2699, 2702, 2712, 2716, 2753, 2774, 2804, 2808, 2821, 2849
    ] :=
  ⟨noS7R12_Law2675, noS7R12_Law2679, noS7R12_Law2683, noS7R12_Law2688, noS7R12_Law2691, noS7R12_Law2699, noS7R12_Law2702, noS7R12_Law2712, noS7R12_Law2716, noS7R12_Law2753, noS7R12_Law2774, noS7R12_Law2804, noS7R12_Law2808, noS7R12_Law2821, noS7R12_Law2849⟩
