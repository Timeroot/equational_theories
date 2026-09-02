import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 22 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 3,833 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4128 takes them (3002 nodes). -/
def ordS10R803_Law4128 : List (Fin 8) := [3, 2, 7, 6, 0, 1, 5, 4]

/-- No member of the class satisfies equation 4128. -/
theorem noS10R803_Law4128 : ∀ v : Magma.tup10R803,
    ¬ @Equation4128 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4128) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law4128) (by native_decide) v.1 v.2
    ((@Law4128.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4138 takes them (831 nodes). -/
def ordS10R803_Law4138 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4138. -/
theorem noS10R803_Law4138 : ∀ v : Magma.tup10R803,
    ¬ @Equation4138 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4138) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law4138) (by native_decide) v.1 v.2
    ((@Law4138.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R803_refutes_21 :
    FamilyRefutes Magma.srch10R803 [
      4128, 4138
    ] :=
  ⟨noS10R803_Law4128, noS10R803_Law4138⟩
