import equational_theories.Definability.Srch_S9R2000

/-!
# Structural certificate targets: `Magma.srch9R2000` (part 222 of 225)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R2000_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,669 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R2000_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4171 takes them (1703 nodes). -/
def ordS9R2000_Law4171 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4171. -/
theorem noS9R2000_Law4171 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4171 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4171) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law4171) (by native_decide) v.1 v.2
    ((@Law4171.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4183 takes them (983 nodes). -/
def ordS9R2000_Law4183 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4183. -/
theorem noS9R2000_Law4183 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4183 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4183) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 3)
    (ord := ordS9R2000_Law4183) (by native_decide) v.1 v.2
    ((@Law4183.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4187 takes them (983 nodes). -/
def ordS9R2000_Law4187 : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- No member of the class satisfies equation 4187. -/
theorem noS9R2000_Law4187 : ∀ v : Magma.tup9R2000,
    ¬ @Equation4187 (Fin 9) (Magma.srch9R2000 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4187) (E := S9R2000.E) (tr := S9R2000.tr) (z := S9R2000.z)
    (st := S9R2000.st) (X := S9R2000.X) (envs := Magma.envsRed 9 S9R2000.E 4)
    (ord := ordS9R2000_Law4187) (by native_decide) v.1 v.2
    ((@Law4187.models_iff (Fin 9) (Magma.srch9R2000 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch9R2000_refutes_221 :
    FamilyRefutes Magma.srch9R2000 [
      4171, 4183, 4187
    ] :=
  ⟨noS9R2000_Law4171, noS9R2000_Law4183, noS9R2000_Law4187⟩
