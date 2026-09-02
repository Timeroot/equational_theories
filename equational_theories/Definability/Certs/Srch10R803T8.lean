import equational_theories.Definability.Srch_S10R803

/-!
# Structural certificate targets: `Magma.srch10R803` (part 9 of 32)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R803_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 2,895 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R803_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2446 takes them (1694 nodes). -/
def ordS10R803_Law2446 : List (Fin 8) := [0, 3, 6, 2, 1, 7, 4, 5]

/-- No member of the class satisfies equation 2446. -/
theorem noS10R803_Law2446 : ∀ v : Magma.tup10R803,
    ¬ @Equation2446 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2446) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 2)
    (ord := ordS10R803_Law2446) (by native_decide) v.1 v.2
    ((@Law2446.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2452 takes them (663 nodes). -/
def ordS10R803_Law2452 : List (Fin 8) := [7, 4, 0, 1, 2, 6, 3, 5]

/-- No member of the class satisfies equation 2452. -/
theorem noS10R803_Law2452 : ∀ v : Magma.tup10R803,
    ¬ @Equation2452 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2452) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2452) (by native_decide) v.1 v.2
    ((@Law2452.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2462 takes them (538 nodes). -/
def ordS10R803_Law2462 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2462. -/
theorem noS10R803_Law2462 : ∀ v : Magma.tup10R803,
    ¬ @Equation2462 (Fin 10) (Magma.srch10R803 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2462) (E := S10R803.E) (tr := S10R803.tr) (z := S10R803.z)
    (st := S10R803.st) (X := S10R803.X) (envs := Magma.envsRed 10 S10R803.E 3)
    (ord := ordS10R803_Law2462) (by native_decide) v.1 v.2
    ((@Law2462.models_iff (Fin 10) (Magma.srch10R803 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R803_refutes_8 :
    FamilyRefutes Magma.srch10R803 [
      2446, 2452, 2462
    ] :=
  ⟨noS10R803_Law2446, noS10R803_Law2452, noS10R803_Law2462⟩
