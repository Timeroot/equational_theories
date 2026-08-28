import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 38 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `8` equations here, 3,631 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3546 takes them (742 nodes). -/
def ordS7R12_Law3546 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3546. -/
theorem noS7R12_Law3546 : ∀ v : Magma.tup7R12,
    ¬ @Equation3546 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3546) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3546) (by native_decide) v.1 v.2
    ((@Law3546.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3548 takes them (93 nodes). -/
def ordS7R12_Law3548 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3548. -/
theorem noS7R12_Law3548 : ∀ v : Magma.tup7R12,
    ¬ @Equation3548 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3548) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3548) (by native_decide) v.1 v.2
    ((@Law3548.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3549 takes them (390 nodes). -/
def ordS7R12_Law3549 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3549. -/
theorem noS7R12_Law3549 : ∀ v : Magma.tup7R12,
    ¬ @Equation3549 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3549) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3549) (by native_decide) v.1 v.2
    ((@Law3549.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3556 takes them (397 nodes). -/
def ordS7R12_Law3556 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3556. -/
theorem noS7R12_Law3556 : ∀ v : Magma.tup7R12,
    ¬ @Equation3556 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3558 takes them (577 nodes). -/
def ordS7R12_Law3558 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3558. -/
theorem noS7R12_Law3558 : ∀ v : Magma.tup7R12,
    ¬ @Equation3558 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3558) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3558) (by native_decide) v.1 v.2
    ((@Law3558.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3566 takes them (88 nodes). -/
def ordS7R12_Law3566 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3566. -/
theorem noS7R12_Law3566 : ∀ v : Magma.tup7R12,
    ¬ @Equation3566 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3566) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3566) (by native_decide) v.1 v.2
    ((@Law3566.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3573 takes them (540 nodes). -/
def ordS7R12_Law3573 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3573. -/
theorem noS7R12_Law3573 : ∀ v : Magma.tup7R12,
    ¬ @Equation3573 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3573) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3573) (by native_decide) v.1 v.2
    ((@Law3573.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3714 takes them (804 nodes). -/
def ordS7R12_Law3714 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3714. -/
theorem noS7R12_Law3714 : ∀ v : Magma.tup7R12,
    ¬ @Equation3714 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3714) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3714) (by native_decide) v.1 v.2
    ((@Law3714.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `8` equations. -/
theorem srch7R12_refutes_37 :
    FamilyRefutes Magma.srch7R12 [
      3546, 3548, 3549, 3556, 3558, 3566, 3573, 3714
    ] :=
  ⟨noS7R12_Law3546, noS7R12_Law3548, noS7R12_Law3549, noS7R12_Law3556, noS7R12_Law3558, noS7R12_Law3566, noS7R12_Law3573, noS7R12_Law3714⟩
