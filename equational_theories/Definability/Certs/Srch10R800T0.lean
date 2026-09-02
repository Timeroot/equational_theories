import equational_theories.Definability.Srch_S10R800

/-!
# Structural certificate targets: `Magma.srch10R800`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S10R800_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 50 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S10R800_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3513 takes them (25 nodes). -/
def ordS10R800_Law3513 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3513. -/
theorem noS10R800_Law3513 : ∀ v : Magma.tup10R800,
    ¬ @Equation3513 (Fin 10) (Magma.srch10R800 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3513) (E := S10R800.E) (tr := S10R800.tr) (z := S10R800.z)
    (st := S10R800.st) (X := S10R800.X) (envs := Magma.envsRed 10 S10R800.E 3)
    (ord := ordS10R800_Law3513) (by native_decide) v.1 v.2
    ((@Law3513.models_iff (Fin 10) (Magma.srch10R800 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3993 takes them (25 nodes). -/
def ordS10R800_Law3993 : List (Fin 6) := [0, 1, 2, 3, 4, 5]

/-- No member of the class satisfies equation 3993. -/
theorem noS10R800_Law3993 : ∀ v : Magma.tup10R800,
    ¬ @Equation3993 (Fin 10) (Magma.srch10R800 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3993) (E := S10R800.E) (tr := S10R800.tr) (z := S10R800.z)
    (st := S10R800.st) (X := S10R800.X) (envs := Magma.envsRed 10 S10R800.E 3)
    (ord := ordS10R800_Law3993) (by native_decide) v.1 v.2
    ((@Law3993.models_iff (Fin 10) (Magma.srch10R800 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch10R800_refutes_0 :
    FamilyRefutes Magma.srch10R800 [
      3513, 3993
    ] :=
  ⟨noS10R800_Law3513, noS10R800_Law3993⟩
