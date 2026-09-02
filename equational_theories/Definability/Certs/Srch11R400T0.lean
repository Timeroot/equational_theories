import equational_theories.Definability.Srch_S11R400

/-!
# Structural certificate targets: `Magma.srch11R400`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R400_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 230 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R400_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3556 takes them (115 nodes). -/
def ordS11R400_Law3556 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3556. -/
theorem noS11R400_Law3556 : ∀ v : Magma.tup11R400,
    ¬ @Equation3556 (Fin 11) (Magma.srch11R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S11R400.E) (tr := S11R400.tr) (z := S11R400.z)
    (st := S11R400.st) (X := S11R400.X) (envs := Magma.envsRed 11 S11R400.E 2)
    (ord := ordS11R400_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 11) (Magma.srch11R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3924 takes them (115 nodes). -/
def ordS11R400_Law3924 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3924. -/
theorem noS11R400_Law3924 : ∀ v : Magma.tup11R400,
    ¬ @Equation3924 (Fin 11) (Magma.srch11R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S11R400.E) (tr := S11R400.tr) (z := S11R400.z)
    (st := S11R400.st) (X := S11R400.X) (envs := Magma.envsRed 11 S11R400.E 2)
    (ord := ordS11R400_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 11) (Magma.srch11R400 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch11R400_refutes_0 :
    FamilyRefutes Magma.srch11R400 [
      3556, 3924
    ] :=
  ⟨noS11R400_Law3556, noS11R400_Law3924⟩
