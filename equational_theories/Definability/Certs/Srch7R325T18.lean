import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 19 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `6` equations here, 68 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4551 takes them (10 nodes). -/
def ordS7R325_Law4551 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4551. -/
theorem noS7R325_Law4551 : ∀ v : Magma.tup7R325,
    ¬ @Equation4551 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4551) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4551) (by native_decide) v.1 v.2
    ((@Law4551.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4572 takes them (10 nodes). -/
def ordS7R325_Law4572 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4572. -/
theorem noS7R325_Law4572 : ∀ v : Magma.tup7R325,
    ¬ @Equation4572 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4572) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4572) (by native_decide) v.1 v.2
    ((@Law4572.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4573 takes them (10 nodes). -/
def ordS7R325_Law4573 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4573. -/
theorem noS7R325_Law4573 : ∀ v : Magma.tup7R325,
    ¬ @Equation4573 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4573) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4573) (by native_decide) v.1 v.2
    ((@Law4573.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4574 takes them (18 nodes). -/
def ordS7R325_Law4574 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4574. -/
theorem noS7R325_Law4574 : ∀ v : Magma.tup7R325,
    ¬ @Equation4574 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4574) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4574) (by native_decide) v.1 v.2
    ((@Law4574.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4575 takes them (10 nodes). -/
def ordS7R325_Law4575 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4575. -/
theorem noS7R325_Law4575 : ∀ v : Magma.tup7R325,
    ¬ @Equation4575 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4575) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4575) (by native_decide) v.1 v.2
    ((@Law4575.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4576 takes them (10 nodes). -/
def ordS7R325_Law4576 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4576. -/
theorem noS7R325_Law4576 : ∀ v : Magma.tup7R325,
    ¬ @Equation4576 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4576) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4576) (by native_decide) v.1 v.2
    ((@Law4576.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch7R325_refutes_18 :
    FamilyRefutes Magma.srch7R325 [
      4551, 4572, 4573, 4574, 4575, 4576
    ] :=
  ⟨noS7R325_Law4551, noS7R325_Law4572, noS7R325_Law4573, noS7R325_Law4574, noS7R325_Law4575, noS7R325_Law4576⟩
