import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 3 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `1` equations here, 453 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 489 takes them (453 nodes). -/
def ordS7R306_Law489 : List (Fin 7) := [4, 1, 6, 5, 3, 2, 0]

/-- No member of the class satisfies equation 489. -/
theorem noS7R306_Law489 : ∀ v : Magma.tup7R306,
    ¬ @Equation489 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law489) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law489) (by native_decide) v.1 v.2
    ((@Law489.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `1` equations. -/
theorem srch7R306_refutes_2 :
    FamilyRefutes Magma.srch7R306 [
      489
    ] :=
  noS7R306_Law489
