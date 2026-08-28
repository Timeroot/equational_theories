import equational_theories.Definability.Srch_S8R13

/-!
# Structural certificate targets: `Magma.srch8R13` (part 10 of 85)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,876 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 503 takes them (2582 nodes). -/
def ordS8R13_Law503 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 503. -/
theorem noS8R13_Law503 : ∀ v : Magma.tup8R13,
    ¬ @Equation503 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law503) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 2)
    (ord := ordS8R13_Law503) (by native_decide) v.1 v.2
    ((@Law503.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 516 takes them (113 nodes). -/
def ordS8R13_Law516 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 516. -/
theorem noS8R13_Law516 : ∀ v : Magma.tup8R13,
    ¬ @Equation516 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law516) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law516) (by native_decide) v.1 v.2
    ((@Law516.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 537 takes them (1181 nodes). -/
def ordS8R13_Law537 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 537. -/
theorem noS8R13_Law537 : ∀ v : Magma.tup8R13,
    ¬ @Equation537 (Fin 8) (Magma.srch8R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law537) (E := S8R13.E) (tr := S8R13.tr) (z := S8R13.z)
    (st := S8R13.st) (X := S8R13.X) (envs := Magma.envsRed 8 S8R13.E 3)
    (ord := ordS8R13_Law537) (by native_decide) v.1 v.2
    ((@Law537.models_iff (Fin 8) (Magma.srch8R13 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch8R13_refutes_9 :
    FamilyRefutes Magma.srch8R13 [
      503, 516, 537
    ] :=
  ⟨noS8R13_Law503, noS8R13_Law516, noS8R13_Law537⟩
