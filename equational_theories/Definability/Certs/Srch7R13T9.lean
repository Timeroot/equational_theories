import equational_theories.Definability.Srch_S7R13

/-!
# Structural certificate targets: `Magma.srch7R13` (part 10 of 17)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 2,598 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2485 takes them (733 nodes). -/
def ordS7R13_Law2485 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2485. -/
theorem noS7R13_Law2485 : ∀ v : Magma.tup7R13,
    ¬ @Equation2485 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2653 takes them (337 nodes). -/
def ordS7R13_Law2653 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2653. -/
theorem noS7R13_Law2653 : ∀ v : Magma.tup7R13,
    ¬ @Equation2653 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2653) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law2653) (by native_decide) v.1 v.2
    ((@Law2653.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2663 takes them (273 nodes). -/
def ordS7R13_Law2663 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2663. -/
theorem noS7R13_Law2663 : ∀ v : Magma.tup7R13,
    ¬ @Equation2663 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2663) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law2663) (by native_decide) v.1 v.2
    ((@Law2663.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (1255 nodes). -/
def ordS7R13_Law2850 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2850. -/
theorem noS7R13_Law2850 : ∀ v : Magma.tup7R13,
    ¬ @Equation2850 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch7R13_refutes_9 :
    FamilyRefutes Magma.srch7R13 [
      2485, 2653, 2663, 2850
    ] :=
  ⟨noS7R13_Law2485, noS7R13_Law2653, noS7R13_Law2663, noS7R13_Law2850⟩
