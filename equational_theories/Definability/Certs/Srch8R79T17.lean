import equational_theories.Definability.Srch_S8R79

/-!
# Structural certificate targets: `Magma.srch8R79` (part 18 of 33)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R79_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,492 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R79_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2043 takes them (3291 nodes). -/
def ordS8R79_Law2043 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2043. -/
theorem noS8R79_Law2043 : ∀ v : Magma.tup8R79,
    ¬ @Equation2043 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2043) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 2)
    (ord := ordS8R79_Law2043) (by native_decide) v.1 v.2
    ((@Law2043.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2068 takes them (201 nodes). -/
def ordS8R79_Law2068 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2068. -/
theorem noS8R79_Law2068 : ∀ v : Magma.tup8R79,
    ¬ @Equation2068 (Fin 8) (Magma.srch8R79 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2068) (E := S8R79.E) (tr := S8R79.tr) (z := S8R79.z)
    (st := S8R79.st) (X := S8R79.X) (envs := Magma.envsRed 8 S8R79.E 3)
    (ord := ordS8R79_Law2068) (by native_decide) v.1 v.2
    ((@Law2068.models_iff (Fin 8) (Magma.srch8R79 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch8R79_refutes_17 :
    FamilyRefutes Magma.srch8R79 [
      2043, 2068
    ] :=
  ⟨noS8R79_Law2043, noS8R79_Law2068⟩
