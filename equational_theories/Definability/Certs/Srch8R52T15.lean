import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 16 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `14` equations here, 3,258 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3546 takes them (326 nodes). -/
def ordS8R52_Law3546 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3546. -/
theorem noS8R52_Law3546 : ∀ v : Magma.tup8R52,
    ¬ @Equation3546 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3546) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3546) (by native_decide) v.1 v.2
    ((@Law3546.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3556 takes them (418 nodes). -/
def ordS8R52_Law3556 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3556. -/
theorem noS8R52_Law3556 : ∀ v : Magma.tup8R52,
    ¬ @Equation3556 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3660 takes them (155 nodes). -/
def ordS8R52_Law3660 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3660. -/
theorem noS8R52_Law3660 : ∀ v : Magma.tup8R52,
    ¬ @Equation3660 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3660) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3660) (by native_decide) v.1 v.2
    ((@Law3660.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3668 takes them (221 nodes). -/
def ordS8R52_Law3668 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3668. -/
theorem noS8R52_Law3668 : ∀ v : Magma.tup8R52,
    ¬ @Equation3668 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3668) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3668) (by native_decide) v.1 v.2
    ((@Law3668.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3674 takes them (165 nodes). -/
def ordS8R52_Law3674 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3674. -/
theorem noS8R52_Law3674 : ∀ v : Magma.tup8R52,
    ¬ @Equation3674 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3674) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3674) (by native_decide) v.1 v.2
    ((@Law3674.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3687 takes them (221 nodes). -/
def ordS8R52_Law3687 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3687. -/
theorem noS8R52_Law3687 : ∀ v : Magma.tup8R52,
    ¬ @Equation3687 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3687) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3687) (by native_decide) v.1 v.2
    ((@Law3687.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3721 takes them (251 nodes). -/
def ordS8R52_Law3721 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3721. -/
theorem noS8R52_Law3721 : ∀ v : Magma.tup8R52,
    ¬ @Equation3721 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3721) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3721) (by native_decide) v.1 v.2
    ((@Law3721.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3723 takes them (147 nodes). -/
def ordS8R52_Law3723 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3723. -/
theorem noS8R52_Law3723 : ∀ v : Magma.tup8R52,
    ¬ @Equation3723 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3723) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3723) (by native_decide) v.1 v.2
    ((@Law3723.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3728 takes them (273 nodes). -/
def ordS8R52_Law3728 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3728. -/
theorem noS8R52_Law3728 : ∀ v : Magma.tup8R52,
    ¬ @Equation3728 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3728) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3728) (by native_decide) v.1 v.2
    ((@Law3728.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3732 takes them (266 nodes). -/
def ordS8R52_Law3732 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3732. -/
theorem noS8R52_Law3732 : ∀ v : Magma.tup8R52,
    ¬ @Equation3732 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3732) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3732) (by native_decide) v.1 v.2
    ((@Law3732.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3759 takes them (253 nodes). -/
def ordS8R52_Law3759 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3759. -/
theorem noS8R52_Law3759 : ∀ v : Magma.tup8R52,
    ¬ @Equation3759 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3759) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3759) (by native_decide) v.1 v.2
    ((@Law3759.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3803 takes them (153 nodes). -/
def ordS8R52_Law3803 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3803. -/
theorem noS8R52_Law3803 : ∀ v : Magma.tup8R52,
    ¬ @Equation3803 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3803) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3803) (by native_decide) v.1 v.2
    ((@Law3803.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3871 takes them (221 nodes). -/
def ordS8R52_Law3871 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3871. -/
theorem noS8R52_Law3871 : ∀ v : Magma.tup8R52,
    ¬ @Equation3871 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3871) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law3871) (by native_decide) v.1 v.2
    ((@Law3871.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3921 takes them (188 nodes). -/
def ordS8R52_Law3921 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3921. -/
theorem noS8R52_Law3921 : ∀ v : Magma.tup8R52,
    ¬ @Equation3921 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3921) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law3921) (by native_decide) v.1 v.2
    ((@Law3921.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `14` equations. -/
theorem srch8R52_refutes_15 :
    FamilyRefutes Magma.srch8R52 [
      3546, 3556, 3660, 3668, 3674, 3687, 3721, 3723, 3728, 3732, 3759, 3803, 3871, 3921
    ] :=
  ⟨noS8R52_Law3546, noS8R52_Law3556, noS8R52_Law3660, noS8R52_Law3668, noS8R52_Law3674, noS8R52_Law3687, noS8R52_Law3721, noS8R52_Law3723, noS8R52_Law3728, noS8R52_Law3732, noS8R52_Law3759, noS8R52_Law3803, noS8R52_Law3871, noS8R52_Law3921⟩
