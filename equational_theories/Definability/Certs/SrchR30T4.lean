import equational_theories.Definability.Srch_SR30

/-!
# Structural certificate targets: `Magma.srchR30` (part 5 of 28)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR30_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `2`
equations here, 3,537 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR30_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1045 takes them (1844 nodes). -/
def ordSR30_Law1045 : List (Fin 10) := [4, 2, 1, 3, 6, 0, 7, 8, 5, 9]

/-- No member of the class satisfies equation 1045. -/
theorem noSR30_Law1045 : ∀ v : Magma.tupR30,
    ¬ @Equation1045 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1045) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law1045) (by native_decide) v.1 v.2
    ((@Law1045.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1228 takes them (1693 nodes). -/
def ordSR30_Law1228 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 1228. -/
theorem noSR30_Law1228 : ∀ v : Magma.tupR30,
    ¬ @Equation1228 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1228) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law1228) (by native_decide) v.1 v.2
    ((@Law1228.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- No member of the class satisfies any of these `2` equations. -/
theorem srchR30_refutes_4 :
    FamilyRefutes Magma.srchR30 [
      1045, 1228
    ] :=
  ⟨noSR30_Law1045, noSR30_Law1228⟩
