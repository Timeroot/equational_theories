import equational_theories.Definability.Srch_S8R14

/-!
# Structural certificate targets: `Magma.srch8R14` (part 8 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R14_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,966 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R14_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4075 takes them (1753 nodes). -/
def ordS8R14_Law4075 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4075. -/
theorem noS8R14_Law4075 : ∀ v : Magma.tup8R14,
    ¬ @Equation4075 (Fin 8) (Magma.srch8R14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4075) (E := S8R14.E) (tr := S8R14.tr) (z := S8R14.z)
    (st := S8R14.st) (X := S8R14.X) (envs := Magma.envsRed 8 S8R14.E 3)
    (ord := ordS8R14_Law4075) (by native_decide) v.1 v.2
    ((@Law4075.models_iff (Fin 8) (Magma.srch8R14 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4078 takes them (1213 nodes). -/
def ordS8R14_Law4078 : List (Fin 15) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

/-- No member of the class satisfies equation 4078. -/
theorem noS8R14_Law4078 : ∀ v : Magma.tup8R14,
    ¬ @Equation4078 (Fin 8) (Magma.srch8R14 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4078) (E := S8R14.E) (tr := S8R14.tr) (z := S8R14.z)
    (st := S8R14.st) (X := S8R14.X) (envs := Magma.envsRed 8 S8R14.E 3)
    (ord := ordS8R14_Law4078) (by native_decide) v.1 v.2
    ((@Law4078.models_iff (Fin 8) (Magma.srch8R14 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R14_refutes_7 :
    FamilyRefutes Magma.srch8R14 [
      4075, 4078
    ] :=
  ⟨noS8R14_Law4075, noS8R14_Law4078⟩
