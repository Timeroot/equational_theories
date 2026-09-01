import equational_theories.Definability.Srch_S7R343

/-!
# Structural certificate targets: `Magma.srch7R343` (part 2 of 3)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R343_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,088 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R343_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3737 takes them (1794 nodes). -/
def ordS7R343_Law3737 : List (Fin 19) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- No member of the class satisfies equation 3737. -/
theorem noS7R343_Law3737 : ∀ v : Magma.tup7R343,
    ¬ @Equation3737 (Fin 7) (Magma.srch7R343 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3737) (E := S7R343.E) (tr := S7R343.tr) (z := S7R343.z)
    (st := S7R343.st) (X := S7R343.X) (envs := Magma.envsRed 7 S7R343.E 3)
    (ord := ordS7R343_Law3737) (by native_decide) v.1 v.2
    ((@Law3737.models_iff (Fin 7) (Magma.srch7R343 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3794 takes them (294 nodes). -/
def ordS7R343_Law3794 : List (Fin 19) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

/-- No member of the class satisfies equation 3794. -/
theorem noS7R343_Law3794 : ∀ v : Magma.tup7R343,
    ¬ @Equation3794 (Fin 7) (Magma.srch7R343 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3794) (E := S7R343.E) (tr := S7R343.tr) (z := S7R343.z)
    (st := S7R343.st) (X := S7R343.X) (envs := Magma.envsRed 7 S7R343.E 3)
    (ord := ordS7R343_Law3794) (by native_decide) v.1 v.2
    ((@Law3794.models_iff (Fin 7) (Magma.srch7R343 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch7R343_refutes_1 :
    FamilyRefutes Magma.srch7R343 [
      3737, 3794
    ] :=
  ⟨noS7R343_Law3737, noS7R343_Law3794⟩
