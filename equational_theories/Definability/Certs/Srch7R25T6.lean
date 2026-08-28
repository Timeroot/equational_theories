import equational_theories.Definability.Srch_S7R25

/-!
# Structural certificate targets: `Magma.srch7R25` (part 7 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 2,473 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2909 takes them (1339 nodes). -/
def ordS7R25_Law2909 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 2909. -/
theorem noS7R25_Law2909 : ∀ v : Magma.tup7R25,
    ¬ @Equation2909 (Fin 7) (Magma.srch7R25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S7R25.E) (tr := S7R25.tr) (z := S7R25.z)
    (st := S7R25.st) (X := S7R25.X) (envs := Magma.envsRed 7 S7R25.E 2)
    (ord := ordS7R25_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 7) (Magma.srch7R25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (1134 nodes). -/
def ordS7R25_Law3112 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3112. -/
theorem noS7R25_Law3112 : ∀ v : Magma.tup7R25,
    ¬ @Equation3112 (Fin 7) (Magma.srch7R25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S7R25.E) (tr := S7R25.tr) (z := S7R25.z)
    (st := S7R25.st) (X := S7R25.X) (envs := Magma.envsRed 7 S7R25.E 2)
    (ord := ordS7R25_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 7) (Magma.srch7R25 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch7R25_refutes_6 :
    FamilyRefutes Magma.srch7R25 [
      2909, 3112
    ] :=
  ⟨noS7R25_Law2909, noS7R25_Law3112⟩
