import equational_theories.Definability.Srch_SR30

/-!
# Structural certificate targets: `Magma.srchR30` (part 12 of 28)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR30_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `3`
equations here, 1,303 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR30_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3007 takes them (75 nodes). -/
def ordSR30_Law3007 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3007. -/
theorem noSR30_Law3007 : ∀ v : Magma.tupR30,
    ¬ @Equation3007 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3007) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 3)
    (ord := ordSR30_Law3007) (by native_decide) v.1 v.2
    ((@Law3007.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3065 takes them (609 nodes). -/
def ordSR30_Law3065 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3065. -/
theorem noSR30_Law3065 : ∀ v : Magma.tupR30,
    ¬ @Equation3065 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3065) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law3065) (by native_decide) v.1 v.2
    ((@Law3065.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3075 takes them (619 nodes). -/
def ordSR30_Law3075 : List (Fin 10) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

/-- No member of the class satisfies equation 3075. -/
theorem noSR30_Law3075 : ∀ v : Magma.tupR30,
    ¬ @Equation3075 (Fin 6) (Magma.srchR30 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3075) (E := SR30.E) (tr := SR30.tr) (z := SR30.z)
    (st := SR30.st) (X := SR30.X) (envs := Magma.envsRed 6 SR30.E 2)
    (ord := ordSR30_Law3075) (by native_decide) v.1 v.2
    ((@Law3075.models_iff (Fin 6) (Magma.srchR30 v)).mpr hv)

/-- No member of the class satisfies any of these `3` equations. -/
theorem srchR30_refutes_11 :
    FamilyRefutes Magma.srchR30 [
      3007, 3065, 3075
    ] :=
  ⟨noSR30_Law3007, noSR30_Law3065, noSR30_Law3075⟩
