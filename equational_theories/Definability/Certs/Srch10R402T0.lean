import equational_theories.Definability.Srch_S10R402

/-!
# Structural certificate targets: `Magma.srch10R402`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R402_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 24 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R402_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4283 takes them (12 nodes). -/
def ordS10R402_Law4283 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4283. -/
theorem noS10R402_Law4283 : ∀ v : Magma.tup10R402,
    ¬ @Equation4283 (Fin 10) (Magma.srch10R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S10R402.E) (tr := S10R402.tr) (z := S10R402.z)
    (st := S10R402.st) (X := S10R402.X) (envs := Magma.envsRed 10 S10R402.E 2)
    (ord := ordS10R402_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 10) (Magma.srch10R402 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (12 nodes). -/
def ordS10R402_Law4635 : List (Fin 3) := [0, 1, 2]

/-- No member of the class satisfies equation 4635. -/
theorem noS10R402_Law4635 : ∀ v : Magma.tup10R402,
    ¬ @Equation4635 (Fin 10) (Magma.srch10R402 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S10R402.E) (tr := S10R402.tr) (z := S10R402.z)
    (st := S10R402.st) (X := S10R402.X) (envs := Magma.envsRed 10 S10R402.E 2)
    (ord := ordS10R402_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 10) (Magma.srch10R402 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R402_refutes_0 :
    FamilyRefutes Magma.srch10R402 [
      4283, 4635
    ] :=
  ⟨noS10R402_Law4283, noS10R402_Law4635⟩
