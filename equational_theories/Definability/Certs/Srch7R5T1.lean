import equational_theories.Definability.Srch_S7R5

/-!
# Structural certificate targets: `Magma.srch7R5` (part 2 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R5_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 1,293 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R5_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 562 takes them (213 nodes). -/
def ordS7R5_Law562 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 562. -/
theorem noS7R5_Law562 : ∀ v : Magma.tup7R5,
    ¬ @Equation562 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law562) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 3)
    (ord := ordS7R5_Law562) (by native_decide) v.1 v.2
    ((@Law562.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 731 takes them (1080 nodes). -/
def ordS7R5_Law731 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 731. -/
theorem noS7R5_Law731 : ∀ v : Magma.tup7R5,
    ¬ @Equation731 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law731) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 3)
    (ord := ordS7R5_Law731) (by native_decide) v.1 v.2
    ((@Law731.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch7R5_refutes_1 :
    FamilyRefutes Magma.srch7R5 [
      562, 731
    ] :=
  ⟨noS7R5_Law562, noS7R5_Law731⟩
