import equational_theories.Definability.Srch_S10R400

/-!
# Structural certificate targets: `Magma.srch10R400` (part 5 of 5)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R400_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,370 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R400_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4158 takes them (2073 nodes). -/
def ordS10R400_Law4158 : List (Fin 11) := [5, 9, 4, 10, 3, 6, 8, 2, 7, 1, 0]

/-- No member of the class satisfies equation 4158. -/
theorem noS10R400_Law4158 : ∀ v : Magma.tup10R400,
    ¬ @Equation4158 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4158) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law4158) (by native_decide) v.1 v.2
    ((@Law4158.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4167 takes them (1150 nodes). -/
def ordS10R400_Law4167 : List (Fin 11) := [8, 3, 0, 4, 2, 7, 5, 10, 9, 1, 6]

/-- No member of the class satisfies equation 4167. -/
theorem noS10R400_Law4167 : ∀ v : Magma.tup10R400,
    ¬ @Equation4167 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4167) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 2)
    (ord := ordS10R400_Law4167) (by native_decide) v.1 v.2
    ((@Law4167.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4229 takes them (147 nodes). -/
def ordS10R400_Law4229 : List (Fin 11) := [6, 5, 4, 9, 8, 7, 2, 1, 10, 0, 3]

/-- No member of the class satisfies equation 4229. -/
theorem noS10R400_Law4229 : ∀ v : Magma.tup10R400,
    ¬ @Equation4229 (Fin 10) (Magma.srch10R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4229) (E := S10R400.E) (tr := S10R400.tr) (z := S10R400.z)
    (st := S10R400.st) (X := S10R400.X) (envs := Magma.envsRed 10 S10R400.E 3)
    (ord := ordS10R400_Law4229) (by native_decide) v.1 v.2
    ((@Law4229.models_iff (Fin 10) (Magma.srch10R400 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R400_refutes_4 :
    FamilyRefutes Magma.srch10R400 [
      4158, 4167, 4229
    ] :=
  ⟨noS10R400_Law4158, noS10R400_Law4167, noS10R400_Law4229⟩
