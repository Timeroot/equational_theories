import equational_theories.Definability.Srch_S7R3

/-!
# Structural certificate targets: `Magma.srch7R3` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R3_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 1,004 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R3_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3997 takes them (352 nodes). -/
def ordS7R3_Law3997 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3997. -/
theorem noS7R3_Law3997 : ∀ v : Magma.tup7R3,
    ¬ @Equation3997 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3997) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law3997) (by native_decide) v.1 v.2
    ((@Law3997.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4200 takes them (652 nodes). -/
def ordS7R3_Law4200 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 4200. -/
theorem noS7R3_Law4200 : ∀ v : Magma.tup7R3,
    ¬ @Equation4200 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4200) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law4200) (by native_decide) v.1 v.2
    ((@Law4200.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch7R3_refutes_1 :
    FamilyRefutes Magma.srch7R3 [
      3997, 4200
    ] :=
  ⟨noS7R3_Law3997, noS7R3_Law4200⟩
