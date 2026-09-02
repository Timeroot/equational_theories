import equational_theories.Definability.Srch_S10R802

/-!
# Structural certificate targets: `Magma.srch10R802` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R802_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `3` equations here, 806 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R802_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2863 takes them (349 nodes). -/
def ordS10R802_Law2863 : List (Fin 8) := [4, 5, 2, 6, 0, 7, 1, 3]

/-- No member of the class satisfies equation 2863. -/
theorem noS10R802_Law2863 : ∀ v : Magma.tup10R802,
    ¬ @Equation2863 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2863) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 2)
    (ord := ordS10R802_Law2863) (by native_decide) v.1 v.2
    ((@Law2863.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4362 takes them (221 nodes). -/
def ordS10R802_Law4362 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4362. -/
theorem noS10R802_Law4362 : ∀ v : Magma.tup10R802,
    ¬ @Equation4362 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4362) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 3)
    (ord := ordS10R802_Law4362) (by native_decide) v.1 v.2
    ((@Law4362.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4673 takes them (236 nodes). -/
def ordS10R802_Law4673 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 4673. -/
theorem noS10R802_Law4673 : ∀ v : Magma.tup10R802,
    ¬ @Equation4673 (Fin 10) (Magma.srch10R802 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4673) (E := S10R802.E) (tr := S10R802.tr) (z := S10R802.z)
    (st := S10R802.st) (X := S10R802.X) (envs := Magma.envsRed 10 S10R802.E 3)
    (ord := ordS10R802_Law4673) (by native_decide) v.1 v.2
    ((@Law4673.models_iff (Fin 10) (Magma.srch10R802 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srch10R802_refutes_1 :
    FamilyRefutes Magma.srch10R802 [
      2863, 4362, 4673
    ] :=
  ⟨noS10R802_Law2863, noS10R802_Law4362, noS10R802_Law4673⟩
