import equational_theories.Definability.Srch_S8R40

/-!
# Structural certificate targets: `Magma.srch8R40` (part 5 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R40_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 558 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R40_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4632 takes them (187 nodes). -/
def ordS8R40_Law4632 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4632. -/
theorem noS8R40_Law4632 : ∀ v : Magma.tup8R40,
    ¬ @Equation4632 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4632) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4632) (by native_decide) v.1 v.2
    ((@Law4632.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4633 takes them (194 nodes). -/
def ordS8R40_Law4633 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4633. -/
theorem noS8R40_Law4633 : ∀ v : Magma.tup8R40,
    ¬ @Equation4633 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4633) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 3)
    (ord := ordS8R40_Law4633) (by native_decide) v.1 v.2
    ((@Law4633.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4634 takes them (43 nodes). -/
def ordS8R40_Law4634 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4634. -/
theorem noS8R40_Law4634 : ∀ v : Magma.tup8R40,
    ¬ @Equation4634 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4634) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4634) (by native_decide) v.1 v.2
    ((@Law4634.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4657 takes them (43 nodes). -/
def ordS8R40_Law4657 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4657. -/
theorem noS8R40_Law4657 : ∀ v : Magma.tup8R40,
    ¬ @Equation4657 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4657) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4657) (by native_decide) v.1 v.2
    ((@Law4657.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4674 takes them (48 nodes). -/
def ordS8R40_Law4674 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4674. -/
theorem noS8R40_Law4674 : ∀ v : Magma.tup8R40,
    ¬ @Equation4674 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4674) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 4)
    (ord := ordS8R40_Law4674) (by native_decide) v.1 v.2
    ((@Law4674.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4676 takes them (43 nodes). -/
def ordS8R40_Law4676 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4676. -/
theorem noS8R40_Law4676 : ∀ v : Magma.tup8R40,
    ¬ @Equation4676 (Fin 8) (Magma.srch8R40 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4676) (E := S8R40.E) (tr := S8R40.tr) (z := S8R40.z)
    (st := S8R40.st) (X := S8R40.X) (envs := Magma.envsRed 8 S8R40.E 5)
    (ord := ordS8R40_Law4676) (by native_decide) v.1 v.2
    ((@Law4676.models_iff (Fin 8) (Magma.srch8R40 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R40_refutes_4 :
    FamilyRefutes Magma.srch8R40 [
      4632, 4633, 4634, 4657, 4674, 4676
    ] :=
  ⟨noS8R40_Law4632, noS8R40_Law4633, noS8R40_Law4634, noS8R40_Law4657, noS8R40_Law4674, noS8R40_Law4676⟩
