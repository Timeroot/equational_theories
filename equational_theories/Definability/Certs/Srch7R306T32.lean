import equational_theories.Definability.Srch_S7R306

/-!
# Structural certificate targets: `Magma.srch7R306` (part 33 of 36)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R306_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `4` equations here, 2,888 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R306_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3878 takes them (468 nodes). -/
def ordS7R306_Law3878 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3878. -/
theorem noS7R306_Law3878 : ∀ v : Magma.tup7R306,
    ¬ @Equation3878 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3878) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law3878) (by native_decide) v.1 v.2
    ((@Law3878.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3994 takes them (407 nodes). -/
def ordS7R306_Law3994 : List (Fin 7) := [1, 4, 3, 6, 2, 0, 5]

/-- No member of the class satisfies equation 3994. -/
theorem noS7R306_Law3994 : ∀ v : Magma.tup7R306,
    ¬ @Equation3994 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3994) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 3)
    (ord := ordS7R306_Law3994) (by native_decide) v.1 v.2
    ((@Law3994.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4081 takes them (1481 nodes). -/
def ordS7R306_Law4081 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4081. -/
theorem noS7R306_Law4081 : ∀ v : Magma.tup7R306,
    ¬ @Equation4081 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4081) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law4081) (by native_decide) v.1 v.2
    ((@Law4081.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4091 takes them (532 nodes). -/
def ordS7R306_Law4091 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4091. -/
theorem noS7R306_Law4091 : ∀ v : Magma.tup7R306,
    ¬ @Equation4091 (Fin 7) (Magma.srch7R306 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4091) (E := S7R306.E) (tr := S7R306.tr) (z := S7R306.z)
    (st := S7R306.st) (X := S7R306.X) (envs := Magma.envsRed 7 S7R306.E 2)
    (ord := ordS7R306_Law4091) (by native_decide) v.1 v.2
    ((@Law4091.models_iff (Fin 7) (Magma.srch7R306 v)).mpr hv)

/-- No member of the class satisfies any of these `4` equations. -/
theorem srch7R306_refutes_32 :
    FamilyRefutes Magma.srch7R306 [
      3878, 3994, 4081, 4091
    ] :=
  ⟨noS7R306_Law3878, noS7R306_Law3994, noS7R306_Law4081, noS7R306_Law4091⟩
