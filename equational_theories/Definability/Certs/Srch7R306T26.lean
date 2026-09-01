import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 27 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 1,011 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2573 takes them (310 nodes). -/
def ordS7R306_Law2573 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2573. -/
theorem noS7R306_Law2573 : ∀ v : Magma.tup7R306,
    ¬ @Equation2573 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2573) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law2573) (by native_decide) v.1 v.2
    ((@Law2573.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2576 takes them (385 nodes). -/
def ordS7R306_Law2576 : List (Fin 7) := [2, 5, 1, 3, 6, 0, 4]

/-- No member of the class satisfies equation 2576. -/
theorem noS7R306_Law2576 : ∀ v : Magma.tup7R306,
    ¬ @Equation2576 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2576) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law2576) (by native_decide) v.1 v.2
    ((@Law2576.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2675 takes them (316 nodes). -/
def ordS7R306_Law2675 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2675. -/
theorem noS7R306_Law2675 : ∀ v : Magma.tup7R306,
    ¬ @Equation2675 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2675) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law2675) (by native_decide) v.1 v.2
    ((@Law2675.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch7R306_refutes_26 :
    FamilyRefutes Magma.srch7R306 [
      2573, 2576, 2675
    ] :=
  ⟨noS7R306_Law2573, noS7R306_Law2576, noS7R306_Law2675⟩
