import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 1 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 1,576 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 14 takes them (351 nodes). -/
def ordS7R306_Law14 : List (Fin 7) := [1, 6, 4, 2, 0, 3, 5]

/-- No member of the class satisfies equation 14. -/
theorem noS7R306_Law14 : ∀ v : Magma.tup7R306,
    ¬ @Equation14 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law14) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law14) (by native_decide) v.1 v.2
    ((@Law14.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 29 takes them (447 nodes). -/
def ordS7R306_Law29 : List (Fin 7) := [5, 0, 3, 6, 2, 4, 1]

/-- No member of the class satisfies equation 29. -/
theorem noS7R306_Law29 : ∀ v : Magma.tup7R306,
    ¬ @Equation29 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law29) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law29) (by native_decide) v.1 v.2
    ((@Law29.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 313 takes them (389 nodes). -/
def ordS7R306_Law313 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 313. -/
theorem noS7R306_Law313 : ∀ v : Magma.tup7R306,
    ¬ @Equation313 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law313) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law313) (by native_decide) v.1 v.2
    ((@Law313.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 365 takes them (389 nodes). -/
def ordS7R306_Law365 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 365. -/
theorem noS7R306_Law365 : ∀ v : Magma.tup7R306,
    ¬ @Equation365 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law365) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law365) (by native_decide) v.1 v.2
    ((@Law365.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch7R306_refutes_0 :
    FamilyRefutes Magma.srch7R306 [
      14, 29, 313, 365
    ] :=
  ⟨noS7R306_Law14, noS7R306_Law29, noS7R306_Law313, noS7R306_Law365⟩
