import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 18 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `20` equations here, 151 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4671 takes them (6 nodes). -/
def ordS8R164_Law4671 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4671. -/
theorem noS8R164_Law4671 : ∀ v : Magma.tup8R164,
    ¬ @Equation4671 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4671) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4671) (by native_decide) v.1 v.2
    ((@Law4671.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4672 takes them (9 nodes). -/
def ordS8R164_Law4672 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4672. -/
theorem noS8R164_Law4672 : ∀ v : Magma.tup8R164,
    ¬ @Equation4672 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4672) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4672) (by native_decide) v.1 v.2
    ((@Law4672.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4674 takes them (9 nodes). -/
def ordS8R164_Law4674 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4674. -/
theorem noS8R164_Law4674 : ∀ v : Magma.tup8R164,
    ¬ @Equation4674 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4674) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4674) (by native_decide) v.1 v.2
    ((@Law4674.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4675 takes them (13 nodes). -/
def ordS8R164_Law4675 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4675. -/
theorem noS8R164_Law4675 : ∀ v : Magma.tup8R164,
    ¬ @Equation4675 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4675) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4675) (by native_decide) v.1 v.2
    ((@Law4675.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4676 takes them (9 nodes). -/
def ordS8R164_Law4676 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4676. -/
theorem noS8R164_Law4676 : ∀ v : Magma.tup8R164,
    ¬ @Equation4676 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4676) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4676) (by native_decide) v.1 v.2
    ((@Law4676.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4678 takes them (6 nodes). -/
def ordS8R164_Law4678 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4678. -/
theorem noS8R164_Law4678 : ∀ v : Magma.tup8R164,
    ¬ @Equation4678 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4678) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4678) (by native_decide) v.1 v.2
    ((@Law4678.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4680 takes them (6 nodes). -/
def ordS8R164_Law4680 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4680. -/
theorem noS8R164_Law4680 : ∀ v : Magma.tup8R164,
    ¬ @Equation4680 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4680) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4680) (by native_decide) v.1 v.2
    ((@Law4680.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4681 takes them (6 nodes). -/
def ordS8R164_Law4681 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4681. -/
theorem noS8R164_Law4681 : ∀ v : Magma.tup8R164,
    ¬ @Equation4681 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4681) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4681) (by native_decide) v.1 v.2
    ((@Law4681.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4682 takes them (10 nodes). -/
def ordS8R164_Law4682 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4682. -/
theorem noS8R164_Law4682 : ∀ v : Magma.tup8R164,
    ¬ @Equation4682 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4682) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4682) (by native_decide) v.1 v.2
    ((@Law4682.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4683 takes them (6 nodes). -/
def ordS8R164_Law4683 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4683. -/
theorem noS8R164_Law4683 : ∀ v : Magma.tup8R164,
    ¬ @Equation4683 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4683) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4683) (by native_decide) v.1 v.2
    ((@Law4683.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4685 takes them (6 nodes). -/
def ordS8R164_Law4685 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4685. -/
theorem noS8R164_Law4685 : ∀ v : Magma.tup8R164,
    ¬ @Equation4685 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4685) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4685) (by native_decide) v.1 v.2
    ((@Law4685.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4686 takes them (7 nodes). -/
def ordS8R164_Law4686 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4686. -/
theorem noS8R164_Law4686 : ∀ v : Magma.tup8R164,
    ¬ @Equation4686 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4686) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4686) (by native_decide) v.1 v.2
    ((@Law4686.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4687 takes them (7 nodes). -/
def ordS8R164_Law4687 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4687. -/
theorem noS8R164_Law4687 : ∀ v : Magma.tup8R164,
    ¬ @Equation4687 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4687) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4687) (by native_decide) v.1 v.2
    ((@Law4687.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4688 takes them (6 nodes). -/
def ordS8R164_Law4688 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4688. -/
theorem noS8R164_Law4688 : ∀ v : Magma.tup8R164,
    ¬ @Equation4688 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4688) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4688) (by native_decide) v.1 v.2
    ((@Law4688.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4689 takes them (10 nodes). -/
def ordS8R164_Law4689 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4689. -/
theorem noS8R164_Law4689 : ∀ v : Magma.tup8R164,
    ¬ @Equation4689 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4689) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4689) (by native_decide) v.1 v.2
    ((@Law4689.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4690 takes them (6 nodes). -/
def ordS8R164_Law4690 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4690. -/
theorem noS8R164_Law4690 : ∀ v : Magma.tup8R164,
    ¬ @Equation4690 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4690) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4690) (by native_decide) v.1 v.2
    ((@Law4690.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4691 takes them (7 nodes). -/
def ordS8R164_Law4691 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4691. -/
theorem noS8R164_Law4691 : ∀ v : Magma.tup8R164,
    ¬ @Equation4691 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4691) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law4691) (by native_decide) v.1 v.2
    ((@Law4691.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4692 takes them (6 nodes). -/
def ordS8R164_Law4692 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4692. -/
theorem noS8R164_Law4692 : ∀ v : Magma.tup8R164,
    ¬ @Equation4692 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4692) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4692) (by native_decide) v.1 v.2
    ((@Law4692.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4693 takes them (10 nodes). -/
def ordS8R164_Law4693 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4693. -/
theorem noS8R164_Law4693 : ∀ v : Magma.tup8R164,
    ¬ @Equation4693 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4693) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law4693) (by native_decide) v.1 v.2
    ((@Law4693.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4694 takes them (6 nodes). -/
def ordS8R164_Law4694 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 4694. -/
theorem noS8R164_Law4694 : ∀ v : Magma.tup8R164,
    ¬ @Equation4694 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4694) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 6)
    (ord := ordS8R164_Law4694) (by native_decide) v.1 v.2
    ((@Law4694.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch8R164_refutes_17 :
    FamilyRefutes Magma.srch8R164 [
      4671, 4672, 4674, 4675, 4676, 4678, 4680, 4681, 4682, 4683, 4685, 4686, 4687, 4688, 4689,
      4690, 4691, 4692, 4693, 4694
    ] :=
  ⟨noS8R164_Law4671, noS8R164_Law4672, noS8R164_Law4674, noS8R164_Law4675, noS8R164_Law4676, noS8R164_Law4678, noS8R164_Law4680, noS8R164_Law4681, noS8R164_Law4682, noS8R164_Law4683, noS8R164_Law4685, noS8R164_Law4686, noS8R164_Law4687, noS8R164_Law4688, noS8R164_Law4689, noS8R164_Law4690, noS8R164_Law4691, noS8R164_Law4692, noS8R164_Law4693, noS8R164_Law4694⟩
