import equational_theories.Definability.Srch_S9R700

/-!
# Structural certificate targets: `Magma.srch9R700` (part 2 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R700_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,671 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R700_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1840 takes them (3176 nodes). -/
def ordS9R700_Law1840 : List (Fin 11) := [2, 8, 9, 5, 7, 3, 0, 10, 4, 1, 6]

/-- No member of the class satisfies equation 1840. -/
theorem noS9R700_Law1840 : ∀ v : Magma.tup9R700,
    ¬ @Equation1840 (Fin 9) (Magma.srch9R700 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1840) (E := S9R700.E) (tr := S9R700.tr) (z := S9R700.z)
    (st := S9R700.st) (X := S9R700.X) (envs := Magma.envsRed 9 S9R700.E 2)
    (ord := ordS9R700_Law1840) (by native_decide) v.1 v.2
    ((@Law1840.models_iff (Fin 9) (Magma.srch9R700 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3520 takes them (495 nodes). -/
def ordS9R700_Law3520 : List (Fin 11) := [10, 6, 7, 8, 9, 2, 0, 5, 3, 1, 4]

/-- No member of the class satisfies equation 3520. -/
theorem noS9R700_Law3520 : ∀ v : Magma.tup9R700,
    ¬ @Equation3520 (Fin 9) (Magma.srch9R700 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3520) (E := S9R700.E) (tr := S9R700.tr) (z := S9R700.z)
    (st := S9R700.st) (X := S9R700.X) (envs := Magma.envsRed 9 S9R700.E 3)
    (ord := ordS9R700_Law3520) (by native_decide) v.1 v.2
    ((@Law3520.models_iff (Fin 9) (Magma.srch9R700 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch9R700_refutes_1 :
    FamilyRefutes Magma.srch9R700 [
      1840, 3520
    ] :=
  ⟨noS9R700_Law1840, noS9R700_Law3520⟩
