import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 7 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `7` equations here, 3,516 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1640 takes them (235 nodes). -/
def ordS10R803_Law1640 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1640. -/
theorem noS10R803_Law1640 : ∀ v : Magma.tup10R803,
    ¬ @Equation1640 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1640) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1640) (by native_decide) v.1 v.2
    ((@Law1640.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1644 takes them (395 nodes). -/
def ordS10R803_Law1644 : List (Fin 8) := [1, 0, 2, 7, 3, 6, 4, 5]

/-- No member of the class satisfies equation 1644. -/
theorem noS10R803_Law1644 : ∀ v : Magma.tup10R803,
    ¬ @Equation1644 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1644) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law1644) (by native_decide) v.1 v.2
    ((@Law1644.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1650 takes them (304 nodes). -/
def ordS10R803_Law1650 : List (Fin 8) := [7, 2, 6, 0, 3, 1, 5, 4]

/-- No member of the class satisfies equation 1650. -/
theorem noS10R803_Law1650 : ∀ v : Magma.tup10R803,
    ¬ @Equation1650 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1650) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1650) (by native_decide) v.1 v.2
    ((@Law1650.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1834 takes them (912 nodes). -/
def ordS10R803_Law1834 : List (Fin 8) := [0, 4, 6, 2, 3, 7, 1, 5]

/-- No member of the class satisfies equation 1834. -/
theorem noS10R803_Law1834 : ∀ v : Magma.tup10R803,
    ¬ @Equation1834 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1834) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law1834) (by native_decide) v.1 v.2
    ((@Law1834.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1847 takes them (988 nodes). -/
def ordS10R803_Law1847 : List (Fin 8) := [0, 7, 6, 3, 2, 5, 1, 4]

/-- No member of the class satisfies equation 1847. -/
theorem noS10R803_Law1847 : ∀ v : Magma.tup10R803,
    ¬ @Equation1847 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1847) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law1847) (by native_decide) v.1 v.2
    ((@Law1847.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1853 takes them (447 nodes). -/
def ordS10R803_Law1853 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1853. -/
theorem noS10R803_Law1853 : ∀ v : Magma.tup10R803,
    ¬ @Equation1853 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1853) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1853) (by native_decide) v.1 v.2
    ((@Law1853.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1867 takes them (235 nodes). -/
def ordS10R803_Law1867 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1867. -/
theorem noS10R803_Law1867 : ∀ v : Magma.tup10R803,
    ¬ @Equation1867 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1867) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law1867) (by native_decide) v.1 v.2
    ((@Law1867.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch10R803_refutes_6 :
    FamilyRefutes Magma.srch10R803 [
      1640, 1644, 1650, 1834, 1847, 1853, 1867
    ] :=
  ⟨noS10R803_Law1640, noS10R803_Law1644, noS10R803_Law1650, noS10R803_Law1834, noS10R803_Law1847, noS10R803_Law1853, noS10R803_Law1867⟩
