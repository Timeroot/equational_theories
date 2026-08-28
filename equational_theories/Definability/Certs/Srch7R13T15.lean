import equational_theories.Definability.Srch_S7R13

/-!
# Structural certificate targets: `Magma.srch7R13` (part 16 of 17)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R13_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 3,214 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R13_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4307 takes them (728 nodes). -/
def ordS7R13_Law4307 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4307. -/
theorem noS7R13_Law4307 : ∀ v : Magma.tup7R13,
    ¬ @Equation4307 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 3)
    (ord := ordS7R13_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4383 takes them (1255 nodes). -/
def ordS7R13_Law4383 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4383. -/
theorem noS7R13_Law4383 : ∀ v : Magma.tup7R13,
    ¬ @Equation4383 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4383) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law4383) (by native_decide) v.1 v.2
    ((@Law4383.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4399 takes them (1231 nodes). -/
def ordS7R13_Law4399 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4399. -/
theorem noS7R13_Law4399 : ∀ v : Magma.tup7R13,
    ¬ @Equation4399 (Fin 7) (Magma.srch7R13 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4399) (E := S7R13.E) (tr := S7R13.tr) (z := S7R13.z)
    (st := S7R13.st) (X := S7R13.X) (envs := Magma.envsRed 7 S7R13.E 2)
    (ord := ordS7R13_Law4399) (by native_decide) v.1 v.2
    ((@Law4399.models_iff (Fin 7) (Magma.srch7R13 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch7R13_refutes_15 :
    FamilyRefutes Magma.srch7R13 [
      4307, 4383, 4399
    ] :=
  ⟨noS7R13_Law4307, noS7R13_Law4383, noS7R13_Law4399⟩
