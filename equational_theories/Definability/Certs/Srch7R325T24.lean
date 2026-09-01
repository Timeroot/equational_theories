import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 25 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 658 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4681 takes them (10 nodes). -/
def ordS7R325_Law4681 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4681. -/
theorem noS7R325_Law4681 : ∀ v : Magma.tup7R325,
    ¬ @Equation4681 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4681) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4681) (by native_decide) v.1 v.2
    ((@Law4681.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4682 takes them (58 nodes). -/
def ordS7R325_Law4682 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4682. -/
theorem noS7R325_Law4682 : ∀ v : Magma.tup7R325,
    ¬ @Equation4682 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4682) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4682) (by native_decide) v.1 v.2
    ((@Law4682.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4683 takes them (10 nodes). -/
def ordS7R325_Law4683 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4683. -/
theorem noS7R325_Law4683 : ∀ v : Magma.tup7R325,
    ¬ @Equation4683 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4683) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4683) (by native_decide) v.1 v.2
    ((@Law4683.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4684 takes them (424 nodes). -/
def ordS7R325_Law4684 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4684. -/
theorem noS7R325_Law4684 : ∀ v : Magma.tup7R325,
    ¬ @Equation4684 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4684) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4684) (by native_decide) v.1 v.2
    ((@Law4684.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4685 takes them (10 nodes). -/
def ordS7R325_Law4685 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4685. -/
theorem noS7R325_Law4685 : ∀ v : Magma.tup7R325,
    ¬ @Equation4685 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4685) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4685) (by native_decide) v.1 v.2
    ((@Law4685.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4686 takes them (16 nodes). -/
def ordS7R325_Law4686 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4686. -/
theorem noS7R325_Law4686 : ∀ v : Magma.tup7R325,
    ¬ @Equation4686 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4686) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4686) (by native_decide) v.1 v.2
    ((@Law4686.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4687 takes them (16 nodes). -/
def ordS7R325_Law4687 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4687. -/
theorem noS7R325_Law4687 : ∀ v : Magma.tup7R325,
    ¬ @Equation4687 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4687) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4687) (by native_decide) v.1 v.2
    ((@Law4687.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4688 takes them (10 nodes). -/
def ordS7R325_Law4688 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4688. -/
theorem noS7R325_Law4688 : ∀ v : Magma.tup7R325,
    ¬ @Equation4688 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4688) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4688) (by native_decide) v.1 v.2
    ((@Law4688.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4690 takes them (10 nodes). -/
def ordS7R325_Law4690 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4690. -/
theorem noS7R325_Law4690 : ∀ v : Magma.tup7R325,
    ¬ @Equation4690 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4690) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4690) (by native_decide) v.1 v.2
    ((@Law4690.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4691 takes them (16 nodes). -/
def ordS7R325_Law4691 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4691. -/
theorem noS7R325_Law4691 : ∀ v : Magma.tup7R325,
    ¬ @Equation4691 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4691) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4691) (by native_decide) v.1 v.2
    ((@Law4691.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4692 takes them (10 nodes). -/
def ordS7R325_Law4692 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4692. -/
theorem noS7R325_Law4692 : ∀ v : Magma.tup7R325,
    ¬ @Equation4692 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4692) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4692) (by native_decide) v.1 v.2
    ((@Law4692.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4693 takes them (58 nodes). -/
def ordS7R325_Law4693 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4693. -/
theorem noS7R325_Law4693 : ∀ v : Magma.tup7R325,
    ¬ @Equation4693 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4693) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4693) (by native_decide) v.1 v.2
    ((@Law4693.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4694 takes them (10 nodes). -/
def ordS7R325_Law4694 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4694. -/
theorem noS7R325_Law4694 : ∀ v : Magma.tup7R325,
    ¬ @Equation4694 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4694) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 6)
    (ord := ordS7R325_Law4694) (by native_decide) v.1 v.2
    ((@Law4694.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch7R325_refutes_24 :
    FamilyRefutes Magma.srch7R325 [
      4681, 4682, 4683, 4684, 4685, 4686, 4687, 4688, 4690, 4691, 4692, 4693, 4694
    ] :=
  ⟨noS7R325_Law4681, noS7R325_Law4682, noS7R325_Law4683, noS7R325_Law4684, noS7R325_Law4685, noS7R325_Law4686, noS7R325_Law4687, noS7R325_Law4688, noS7R325_Law4690, noS7R325_Law4691, noS7R325_Law4692, noS7R325_Law4693, noS7R325_Law4694⟩
