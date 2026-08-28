import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 39 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `9` equations here, 1,966 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3716 takes them (557 nodes). -/
def ordS7R12_Law3716 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3716. -/
theorem noS7R12_Law3716 : ∀ v : Magma.tup7R12,
    ¬ @Equation3716 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3716) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3716) (by native_decide) v.1 v.2
    ((@Law3716.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3723 takes them (76 nodes). -/
def ordS7R12_Law3723 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3723. -/
theorem noS7R12_Law3723 : ∀ v : Magma.tup7R12,
    ¬ @Equation3723 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3723) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3723) (by native_decide) v.1 v.2
    ((@Law3723.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3726 takes them (82 nodes). -/
def ordS7R12_Law3726 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3726. -/
theorem noS7R12_Law3726 : ∀ v : Magma.tup7R12,
    ¬ @Equation3726 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3726) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3726) (by native_decide) v.1 v.2
    ((@Law3726.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3728 takes them (58 nodes). -/
def ordS7R12_Law3728 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3728. -/
theorem noS7R12_Law3728 : ∀ v : Magma.tup7R12,
    ¬ @Equation3728 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3728) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3728) (by native_decide) v.1 v.2
    ((@Law3728.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3732 takes them (90 nodes). -/
def ordS7R12_Law3732 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3732. -/
theorem noS7R12_Law3732 : ∀ v : Magma.tup7R12,
    ¬ @Equation3732 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3732) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3732) (by native_decide) v.1 v.2
    ((@Law3732.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3748 takes them (269 nodes). -/
def ordS7R12_Law3748 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3748. -/
theorem noS7R12_Law3748 : ∀ v : Magma.tup7R12,
    ¬ @Equation3748 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3748) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3748) (by native_decide) v.1 v.2
    ((@Law3748.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3751 takes them (221 nodes). -/
def ordS7R12_Law3751 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3751. -/
theorem noS7R12_Law3751 : ∀ v : Magma.tup7R12,
    ¬ @Equation3751 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3751) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3751) (by native_decide) v.1 v.2
    ((@Law3751.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3752 takes them (430 nodes). -/
def ordS7R12_Law3752 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3752. -/
theorem noS7R12_Law3752 : ∀ v : Magma.tup7R12,
    ¬ @Equation3752 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3752) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3752) (by native_decide) v.1 v.2
    ((@Law3752.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3756 takes them (183 nodes). -/
def ordS7R12_Law3756 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3756. -/
theorem noS7R12_Law3756 : ∀ v : Magma.tup7R12,
    ¬ @Equation3756 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3756) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3756) (by native_decide) v.1 v.2
    ((@Law3756.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `9` equations. -/
theorem srch7R12_refutes_38 :
    FamilyRefutes Magma.srch7R12 [
      3716, 3723, 3726, 3728, 3732, 3748, 3751, 3752, 3756
    ] :=
  ⟨noS7R12_Law3716, noS7R12_Law3723, noS7R12_Law3726, noS7R12_Law3728, noS7R12_Law3732, noS7R12_Law3748, noS7R12_Law3751, noS7R12_Law3752, noS7R12_Law3756⟩
