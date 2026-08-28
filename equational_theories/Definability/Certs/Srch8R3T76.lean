import equational_theories.Definability.Srch_S8R3

/-!
# Structural certificate targets: `Magma.srch8R3` (part 77 of 77)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R3_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `4`
equations here, 2,384 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R3_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4634 takes them (861 nodes). -/
def ordS8R3_Law4634 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4634. -/
theorem noS8R3_Law4634 : ∀ v : Magma.tup8R3,
    ¬ @Equation4634 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4634) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 4)
    (ord := ordS8R3_Law4634) (by native_decide) v.1 v.2
    ((@Law4634.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4657 takes them (525 nodes). -/
def ordS8R3_Law4657 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4657. -/
theorem noS8R3_Law4657 : ∀ v : Magma.tup8R3,
    ¬ @Equation4657 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4657) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 4)
    (ord := ordS8R3_Law4657) (by native_decide) v.1 v.2
    ((@Law4657.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4674 takes them (525 nodes). -/
def ordS8R3_Law4674 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4674. -/
theorem noS8R3_Law4674 : ∀ v : Magma.tup8R3,
    ¬ @Equation4674 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4674) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 4)
    (ord := ordS8R3_Law4674) (by native_decide) v.1 v.2
    ((@Law4674.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4676 takes them (473 nodes). -/
def ordS8R3_Law4676 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4676. -/
theorem noS8R3_Law4676 : ∀ v : Magma.tup8R3,
    ¬ @Equation4676 (Fin 8) (Magma.srch8R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4676) (E := S8R3.E) (tr := S8R3.tr) (z := S8R3.z)
    (st := S8R3.st) (X := S8R3.X) (envs := Magma.envsRed 8 S8R3.E 5)
    (ord := ordS8R3_Law4676) (by native_decide) v.1 v.2
    ((@Law4676.models_iff (Fin 8) (Magma.srch8R3 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch8R3_refutes_76 :
    FamilyRefutes Magma.srch8R3 [
      4634, 4657, 4674, 4676
    ] :=
  ⟨noS8R3_Law4634, noS8R3_Law4657, noS8R3_Law4674, noS8R3_Law4676⟩
