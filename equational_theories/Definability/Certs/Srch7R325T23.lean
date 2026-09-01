import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 24 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `20` equations here, 3,168 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4654 takes them (255 nodes). -/
def ordS7R325_Law4654 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4654. -/
theorem noS7R325_Law4654 : ∀ v : Magma.tup7R325,
    ¬ @Equation4654 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4654) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4654) (by native_decide) v.1 v.2
    ((@Law4654.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4655 takes them (716 nodes). -/
def ordS7R325_Law4655 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4655. -/
theorem noS7R325_Law4655 : ∀ v : Magma.tup7R325,
    ¬ @Equation4655 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4655) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4655) (by native_decide) v.1 v.2
    ((@Law4655.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4657 takes them (52 nodes). -/
def ordS7R325_Law4657 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4657. -/
theorem noS7R325_Law4657 : ∀ v : Magma.tup7R325,
    ¬ @Equation4657 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4657) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4657) (by native_decide) v.1 v.2
    ((@Law4657.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4659 takes them (147 nodes). -/
def ordS7R325_Law4659 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4659. -/
theorem noS7R325_Law4659 : ∀ v : Magma.tup7R325,
    ¬ @Equation4659 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4659) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4659) (by native_decide) v.1 v.2
    ((@Law4659.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4660 takes them (155 nodes). -/
def ordS7R325_Law4660 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4660. -/
theorem noS7R325_Law4660 : ∀ v : Magma.tup7R325,
    ¬ @Equation4660 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4660) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4660) (by native_decide) v.1 v.2
    ((@Law4660.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4662 takes them (10 nodes). -/
def ordS7R325_Law4662 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4662. -/
theorem noS7R325_Law4662 : ∀ v : Magma.tup7R325,
    ¬ @Equation4662 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4662) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4662) (by native_decide) v.1 v.2
    ((@Law4662.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4663 takes them (893 nodes). -/
def ordS7R325_Law4663 : List (Fin 9) := [7, 5, 0, 6, 2, 1, 8, 4, 3]

/-- No member of the class satisfies equation 4663. -/
theorem noS7R325_Law4663 : ∀ v : Magma.tup7R325,
    ¬ @Equation4663 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4663) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4663) (by native_decide) v.1 v.2
    ((@Law4663.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4664 takes them (10 nodes). -/
def ordS7R325_Law4664 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4664. -/
theorem noS7R325_Law4664 : ∀ v : Magma.tup7R325,
    ¬ @Equation4664 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4664) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4664) (by native_decide) v.1 v.2
    ((@Law4664.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4665 takes them (157 nodes). -/
def ordS7R325_Law4665 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4665. -/
theorem noS7R325_Law4665 : ∀ v : Magma.tup7R325,
    ¬ @Equation4665 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4665) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4665) (by native_decide) v.1 v.2
    ((@Law4665.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4667 takes them (10 nodes). -/
def ordS7R325_Law4667 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4667. -/
theorem noS7R325_Law4667 : ∀ v : Magma.tup7R325,
    ¬ @Equation4667 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4667) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4667) (by native_decide) v.1 v.2
    ((@Law4667.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4668 takes them (16 nodes). -/
def ordS7R325_Law4668 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4668. -/
theorem noS7R325_Law4668 : ∀ v : Magma.tup7R325,
    ¬ @Equation4668 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4668) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4668) (by native_decide) v.1 v.2
    ((@Law4668.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4669 takes them (246 nodes). -/
def ordS7R325_Law4669 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4669. -/
theorem noS7R325_Law4669 : ∀ v : Magma.tup7R325,
    ¬ @Equation4669 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4669) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4669) (by native_decide) v.1 v.2
    ((@Law4669.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4671 takes them (10 nodes). -/
def ordS7R325_Law4671 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4671. -/
theorem noS7R325_Law4671 : ∀ v : Magma.tup7R325,
    ¬ @Equation4671 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4671) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4671) (by native_decide) v.1 v.2
    ((@Law4671.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4672 takes them (52 nodes). -/
def ordS7R325_Law4672 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4672. -/
theorem noS7R325_Law4672 : ∀ v : Magma.tup7R325,
    ¬ @Equation4672 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4672) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4672) (by native_decide) v.1 v.2
    ((@Law4672.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4674 takes them (52 nodes). -/
def ordS7R325_Law4674 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4674. -/
theorem noS7R325_Law4674 : ∀ v : Magma.tup7R325,
    ¬ @Equation4674 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4674) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4674) (by native_decide) v.1 v.2
    ((@Law4674.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4675 takes them (100 nodes). -/
def ordS7R325_Law4675 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4675. -/
theorem noS7R325_Law4675 : ∀ v : Magma.tup7R325,
    ¬ @Equation4675 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4675) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4675) (by native_decide) v.1 v.2
    ((@Law4675.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4676 takes them (52 nodes). -/
def ordS7R325_Law4676 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4676. -/
theorem noS7R325_Law4676 : ∀ v : Magma.tup7R325,
    ¬ @Equation4676 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4676) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4676) (by native_decide) v.1 v.2
    ((@Law4676.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4678 takes them (16 nodes). -/
def ordS7R325_Law4678 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4678. -/
theorem noS7R325_Law4678 : ∀ v : Magma.tup7R325,
    ¬ @Equation4678 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4678) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4678) (by native_decide) v.1 v.2
    ((@Law4678.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4679 takes them (209 nodes). -/
def ordS7R325_Law4679 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4679. -/
theorem noS7R325_Law4679 : ∀ v : Magma.tup7R325,
    ¬ @Equation4679 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4679) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4679) (by native_decide) v.1 v.2
    ((@Law4679.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4680 takes them (10 nodes). -/
def ordS7R325_Law4680 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4680. -/
theorem noS7R325_Law4680 : ∀ v : Magma.tup7R325,
    ¬ @Equation4680 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4680) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4680) (by native_decide) v.1 v.2
    ((@Law4680.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch7R325_refutes_23 :
    FamilyRefutes Magma.srch7R325 [
      4654, 4655, 4657, 4659, 4660, 4662, 4663, 4664, 4665, 4667, 4668, 4669, 4671, 4672, 4674,
      4675, 4676, 4678, 4679, 4680
    ] :=
  ⟨noS7R325_Law4654, noS7R325_Law4655, noS7R325_Law4657, noS7R325_Law4659, noS7R325_Law4660, noS7R325_Law4662, noS7R325_Law4663, noS7R325_Law4664, noS7R325_Law4665, noS7R325_Law4667, noS7R325_Law4668, noS7R325_Law4669, noS7R325_Law4671, noS7R325_Law4672, noS7R325_Law4674, noS7R325_Law4675, noS7R325_Law4676, noS7R325_Law4678, noS7R325_Law4679, noS7R325_Law4680⟩
