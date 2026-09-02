import equational_theories.Definability.Srch_S9R701

/-!
# Structural certificate targets: `Magma.srch9R701`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R701_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 1,300 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R701_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 833 takes them (167 nodes). -/
def ordS9R701_Law833 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 833. -/
theorem noS9R701_Law833 : ∀ v : Magma.tup9R701,
    ¬ @Equation833 (Fin 9) (Magma.srch9R701 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law833) (E := S9R701.E) (tr := S9R701.tr) (z := S9R701.z)
    (st := S9R701.st) (X := S9R701.X) (envs := Magma.envsRed 9 S9R701.E 2)
    (ord := ordS9R701_Law833) (by native_decide) v.1 v.2
    ((@Law833.models_iff (Fin 9) (Magma.srch9R701 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2699 takes them (167 nodes). -/
def ordS9R701_Law2699 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2699. -/
theorem noS9R701_Law2699 : ∀ v : Magma.tup9R701,
    ¬ @Equation2699 (Fin 9) (Magma.srch9R701 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2699) (E := S9R701.E) (tr := S9R701.tr) (z := S9R701.z)
    (st := S9R701.st) (X := S9R701.X) (envs := Magma.envsRed 9 S9R701.E 2)
    (ord := ordS9R701_Law2699) (by native_decide) v.1 v.2
    ((@Law2699.models_iff (Fin 9) (Magma.srch9R701 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3724 takes them (215 nodes). -/
def ordS9R701_Law3724 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3724. -/
theorem noS9R701_Law3724 : ∀ v : Magma.tup9R701,
    ¬ @Equation3724 (Fin 9) (Magma.srch9R701 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3724) (E := S9R701.E) (tr := S9R701.tr) (z := S9R701.z)
    (st := S9R701.st) (X := S9R701.X) (envs := Magma.envsRed 9 S9R701.E 2)
    (ord := ordS9R701_Law3724) (by native_decide) v.1 v.2
    ((@Law3724.models_iff (Fin 9) (Magma.srch9R701 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3749 takes them (215 nodes). -/
def ordS9R701_Law3749 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3749. -/
theorem noS9R701_Law3749 : ∀ v : Magma.tup9R701,
    ¬ @Equation3749 (Fin 9) (Magma.srch9R701 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3749) (E := S9R701.E) (tr := S9R701.tr) (z := S9R701.z)
    (st := S9R701.st) (X := S9R701.X) (envs := Magma.envsRed 9 S9R701.E 2)
    (ord := ordS9R701_Law3749) (by native_decide) v.1 v.2
    ((@Law3749.models_iff (Fin 9) (Magma.srch9R701 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4362 takes them (199 nodes). -/
def ordS9R701_Law4362 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4362. -/
theorem noS9R701_Law4362 : ∀ v : Magma.tup9R701,
    ¬ @Equation4362 (Fin 9) (Magma.srch9R701 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4362) (E := S9R701.E) (tr := S9R701.tr) (z := S9R701.z)
    (st := S9R701.st) (X := S9R701.X) (envs := Magma.envsRed 9 S9R701.E 3)
    (ord := ordS9R701_Law4362) (by native_decide) v.1 v.2
    ((@Law4362.models_iff (Fin 9) (Magma.srch9R701 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4673 takes them (337 nodes). -/
def ordS9R701_Law4673 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4673. -/
theorem noS9R701_Law4673 : ∀ v : Magma.tup9R701,
    ¬ @Equation4673 (Fin 9) (Magma.srch9R701 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4673) (E := S9R701.E) (tr := S9R701.tr) (z := S9R701.z)
    (st := S9R701.st) (X := S9R701.X) (envs := Magma.envsRed 9 S9R701.E 3)
    (ord := ordS9R701_Law4673) (by native_decide) v.1 v.2
    ((@Law4673.models_iff (Fin 9) (Magma.srch9R701 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch9R701_refutes_0 :
    FamilyRefutes Magma.srch9R701 [
      833, 2699, 3724, 3749, 4362, 4673
    ] :=
  ⟨noS9R701_Law833, noS9R701_Law2699, noS9R701_Law3724, noS9R701_Law3749, noS9R701_Law4362, noS9R701_Law4673⟩
