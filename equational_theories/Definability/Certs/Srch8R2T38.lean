import equational_theories.Definability.Srch_S8R2

/-!
# Structural certificate targets: `Magma.srch8R2` (part 39 of 260)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R2_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 2,627 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R2_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 520 takes them (2201 nodes). -/
def ordS8R2_Law520 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 520. -/
theorem noS8R2_Law520 : ∀ v : Magma.tup8R2,
    ¬ @Equation520 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law520) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law520) (by native_decide) v.1 v.2
    ((@Law520.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 524 takes them (213 nodes). -/
def ordS8R2_Law524 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 524. -/
theorem noS8R2_Law524 : ∀ v : Magma.tup8R2,
    ¬ @Equation524 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law524) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law524) (by native_decide) v.1 v.2
    ((@Law524.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 532 takes them (213 nodes). -/
def ordS8R2_Law532 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 532. -/
theorem noS8R2_Law532 : ∀ v : Magma.tup8R2,
    ¬ @Equation532 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law532) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law532) (by native_decide) v.1 v.2
    ((@Law532.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch8R2_refutes_38 :
    FamilyRefutes Magma.srch8R2 [
      520, 524, 532
    ] :=
  ⟨noS8R2_Law520, noS8R2_Law524, noS8R2_Law532⟩
