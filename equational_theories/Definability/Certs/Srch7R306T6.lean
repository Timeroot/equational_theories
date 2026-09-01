import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 7 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 781 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 746 takes them (465 nodes). -/
def ordS7R306_Law746 : List (Fin 7) := [0, 3, 4, 2, 1, 6, 5]

/-- No member of the class satisfies equation 746. -/
theorem noS7R306_Law746 : ∀ v : Magma.tup7R306,
    ¬ @Equation746 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law746) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law746) (by native_decide) v.1 v.2
    ((@Law746.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 860 takes them (316 nodes). -/
def ordS7R306_Law860 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 860. -/
theorem noS7R306_Law860 : ∀ v : Magma.tup7R306,
    ¬ @Equation860 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law860) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law860) (by native_decide) v.1 v.2
    ((@Law860.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch7R306_refutes_6 :
    FamilyRefutes Magma.srch7R306 [
      746, 860
    ] :=
  ⟨noS7R306_Law746, noS7R306_Law860⟩
