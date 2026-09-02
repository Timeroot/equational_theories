import equational_theories.Definability.Srch_S12R400

/-!
# Structural certificate targets: `Magma.srch12R400`

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S12R400_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `2` equations here, 439 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S12R400_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 315 takes them (362 nodes). -/
def ordS12R400_Law315 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 315. -/
theorem noS12R400_Law315 : ∀ v : Magma.tup12R400,
    ¬ @Equation315 (Fin 12) (Magma.srch12R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law315) (E := S12R400.E) (tr := S12R400.tr) (z := S12R400.z)
    (st := S12R400.st) (X := S12R400.X) (envs := Magma.envsRed 12 S12R400.E 2)
    (ord := ordS12R400_Law315) (by native_decide) v.1 v.2
    ((@Law315.models_iff (Fin 12) (Magma.srch12R400 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 362 takes them (77 nodes). -/
def ordS12R400_Law362 : List (Fin 9) := [0, 8, 6, 4, 7, 2, 5, 3, 1]

/-- No member of the class satisfies equation 362. -/
theorem noS12R400_Law362 : ∀ v : Magma.tup12R400,
    ¬ @Equation362 (Fin 12) (Magma.srch12R400 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law362) (E := S12R400.E) (tr := S12R400.tr) (z := S12R400.z)
    (st := S12R400.st) (X := S12R400.X) (envs := Magma.envsRed 12 S12R400.E 2)
    (ord := ordS12R400_Law362) (by native_decide) v.1 v.2
    ((@Law362.models_iff (Fin 12) (Magma.srch12R400 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srch12R400_refutes_0 :
    FamilyRefutes Magma.srch12R400 [
      315, 362
    ] :=
  ⟨noS12R400_Law315, noS12R400_Law362⟩
