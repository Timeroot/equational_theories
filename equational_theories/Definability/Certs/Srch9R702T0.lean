import equational_theories.Definability.Srch_S9R702

/-!
# Structural certificate targets: `Magma.srch9R702`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R702_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 1,091 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R702_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3588 takes them (623 nodes). -/
def ordS9R702_Law3588 : List (Fin 13) := [12, 10, 7, 8, 4, 6, 11, 5, 1, 3, 2, 0, 9]

/-- No member of the class satisfies equation 3588. -/
theorem noS9R702_Law3588 : ∀ v : Magma.tup9R702,
    ¬ @Equation3588 (Fin 9) (Magma.srch9R702 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3588) (E := S9R702.E) (tr := S9R702.tr) (z := S9R702.z)
    (st := S9R702.st) (X := S9R702.X) (envs := Magma.envsRed 9 S9R702.E 3)
    (ord := ordS9R702_Law3588) (by native_decide) v.1 v.2
    ((@Law3588.models_iff (Fin 9) (Magma.srch9R702 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3994 takes them (468 nodes). -/
def ordS9R702_Law3994 : List (Fin 13) := [5, 1, 3, 10, 0, 7, 4, 11, 12, 2, 6, 9, 8]

/-- No member of the class satisfies equation 3994. -/
theorem noS9R702_Law3994 : ∀ v : Magma.tup9R702,
    ¬ @Equation3994 (Fin 9) (Magma.srch9R702 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3994) (E := S9R702.E) (tr := S9R702.tr) (z := S9R702.z)
    (st := S9R702.st) (X := S9R702.X) (envs := Magma.envsRed 9 S9R702.E 3)
    (ord := ordS9R702_Law3994) (by native_decide) v.1 v.2
    ((@Law3994.models_iff (Fin 9) (Magma.srch9R702 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch9R702_refutes_0 :
    FamilyRefutes Magma.srch9R702 [
      3588, 3994
    ] :=
  ⟨noS9R702_Law3588, noS9R702_Law3994⟩
