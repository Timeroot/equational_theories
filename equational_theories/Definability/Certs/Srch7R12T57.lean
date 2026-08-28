import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 58 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `19` equations here, 3,054 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4635 takes them (756 nodes). -/
def ordS7R12_Law4635 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4635. -/
theorem noS7R12_Law4635 : ∀ v : Magma.tup7R12,
    ¬ @Equation4635 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4638 takes them (126 nodes). -/
def ordS7R12_Law4638 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4638. -/
theorem noS7R12_Law4638 : ∀ v : Magma.tup7R12,
    ¬ @Equation4638 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4638) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4638) (by native_decide) v.1 v.2
    ((@Law4638.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4639 takes them (269 nodes). -/
def ordS7R12_Law4639 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4639. -/
theorem noS7R12_Law4639 : ∀ v : Magma.tup7R12,
    ¬ @Equation4639 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4639) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4639) (by native_decide) v.1 v.2
    ((@Law4639.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4640 takes them (85 nodes). -/
def ordS7R12_Law4640 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4640. -/
theorem noS7R12_Law4640 : ∀ v : Magma.tup7R12,
    ¬ @Equation4640 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4640) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4640) (by native_decide) v.1 v.2
    ((@Law4640.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4642 takes them (141 nodes). -/
def ordS7R12_Law4642 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4642. -/
theorem noS7R12_Law4642 : ∀ v : Magma.tup7R12,
    ¬ @Equation4642 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4642) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4642) (by native_decide) v.1 v.2
    ((@Law4642.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4645 takes them (142 nodes). -/
def ordS7R12_Law4645 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4645. -/
theorem noS7R12_Law4645 : ∀ v : Magma.tup7R12,
    ¬ @Equation4645 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4645) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4645) (by native_decide) v.1 v.2
    ((@Law4645.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4646 takes them (46 nodes). -/
def ordS7R12_Law4646 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4646. -/
theorem noS7R12_Law4646 : ∀ v : Magma.tup7R12,
    ¬ @Equation4646 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4646) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4646) (by native_decide) v.1 v.2
    ((@Law4646.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4647 takes them (338 nodes). -/
def ordS7R12_Law4647 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4647. -/
theorem noS7R12_Law4647 : ∀ v : Magma.tup7R12,
    ¬ @Equation4647 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4647) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4647) (by native_decide) v.1 v.2
    ((@Law4647.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4649 takes them (44 nodes). -/
def ordS7R12_Law4649 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4649. -/
theorem noS7R12_Law4649 : ∀ v : Magma.tup7R12,
    ¬ @Equation4649 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4649) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4649) (by native_decide) v.1 v.2
    ((@Law4649.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4651 takes them (257 nodes). -/
def ordS7R12_Law4651 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4651. -/
theorem noS7R12_Law4651 : ∀ v : Magma.tup7R12,
    ¬ @Equation4651 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4651) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4651) (by native_decide) v.1 v.2
    ((@Law4651.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4652 takes them (38 nodes). -/
def ordS7R12_Law4652 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4652. -/
theorem noS7R12_Law4652 : ∀ v : Magma.tup7R12,
    ¬ @Equation4652 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4652) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4652) (by native_decide) v.1 v.2
    ((@Law4652.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4654 takes them (28 nodes). -/
def ordS7R12_Law4654 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4654. -/
theorem noS7R12_Law4654 : ∀ v : Magma.tup7R12,
    ¬ @Equation4654 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4654) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4654) (by native_decide) v.1 v.2
    ((@Law4654.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4655 takes them (166 nodes). -/
def ordS7R12_Law4655 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4655. -/
theorem noS7R12_Law4655 : ∀ v : Magma.tup7R12,
    ¬ @Equation4655 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4655) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4655) (by native_decide) v.1 v.2
    ((@Law4655.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4657 takes them (24 nodes). -/
def ordS7R12_Law4657 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4657. -/
theorem noS7R12_Law4657 : ∀ v : Magma.tup7R12,
    ¬ @Equation4657 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4657) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4657) (by native_decide) v.1 v.2
    ((@Law4657.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4663 takes them (92 nodes). -/
def ordS7R12_Law4663 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4663. -/
theorem noS7R12_Law4663 : ∀ v : Magma.tup7R12,
    ¬ @Equation4663 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4663) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4663) (by native_decide) v.1 v.2
    ((@Law4663.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4669 takes them (24 nodes). -/
def ordS7R12_Law4669 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4669. -/
theorem noS7R12_Law4669 : ∀ v : Magma.tup7R12,
    ¬ @Equation4669 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4669) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4669) (by native_decide) v.1 v.2
    ((@Law4669.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4672 takes them (26 nodes). -/
def ordS7R12_Law4672 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4672. -/
theorem noS7R12_Law4672 : ∀ v : Magma.tup7R12,
    ¬ @Equation4672 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4672) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4672) (by native_decide) v.1 v.2
    ((@Law4672.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4673 takes them (428 nodes). -/
def ordS7R12_Law4673 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4673. -/
theorem noS7R12_Law4673 : ∀ v : Magma.tup7R12,
    ¬ @Equation4673 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4673) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law4673) (by native_decide) v.1 v.2
    ((@Law4673.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4674 takes them (24 nodes). -/
def ordS7R12_Law4674 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 4674. -/
theorem noS7R12_Law4674 : ∀ v : Magma.tup7R12,
    ¬ @Equation4674 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4674) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law4674) (by native_decide) v.1 v.2
    ((@Law4674.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `19` equations. -/
theorem srch7R12_refutes_57 :
    FamilyRefutes Magma.srch7R12 [
      4635, 4638, 4639, 4640, 4642, 4645, 4646, 4647, 4649, 4651, 4652, 4654, 4655, 4657, 4663,
      4669, 4672, 4673, 4674
    ] :=
  ⟨noS7R12_Law4635, noS7R12_Law4638, noS7R12_Law4639, noS7R12_Law4640, noS7R12_Law4642, noS7R12_Law4645, noS7R12_Law4646, noS7R12_Law4647, noS7R12_Law4649, noS7R12_Law4651, noS7R12_Law4652, noS7R12_Law4654, noS7R12_Law4655, noS7R12_Law4657, noS7R12_Law4663, noS7R12_Law4669, noS7R12_Law4672, noS7R12_Law4673, noS7R12_Law4674⟩
