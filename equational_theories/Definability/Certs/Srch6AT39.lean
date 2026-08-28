import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 40 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `20`
equations here, 3,062 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3747 takes them (50 nodes). -/
def ordS6A_Law3747 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3747. -/
theorem noS6A_Law3747 : ∀ v : Magma.tupS6A,
    ¬ @Equation3747 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3747) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3747) (by native_decide) v.1 v.2
    ((@Law3747.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3750 takes them (127 nodes). -/
def ordS6A_Law3750 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3750. -/
theorem noS6A_Law3750 : ∀ v : Magma.tupS6A,
    ¬ @Equation3750 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3750) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3750) (by native_decide) v.1 v.2
    ((@Law3750.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3753 takes them (130 nodes). -/
def ordS6A_Law3753 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3753. -/
theorem noS6A_Law3753 : ∀ v : Magma.tupS6A,
    ¬ @Equation3753 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3753) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3753) (by native_decide) v.1 v.2
    ((@Law3753.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3754 takes them (154 nodes). -/
def ordS6A_Law3754 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3754. -/
theorem noS6A_Law3754 : ∀ v : Magma.tupS6A,
    ¬ @Equation3754 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3754) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3754) (by native_decide) v.1 v.2
    ((@Law3754.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3755 takes them (211 nodes). -/
def ordS6A_Law3755 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3755. -/
theorem noS6A_Law3755 : ∀ v : Magma.tupS6A,
    ¬ @Equation3755 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3755) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3755) (by native_decide) v.1 v.2
    ((@Law3755.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3757 takes them (120 nodes). -/
def ordS6A_Law3757 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3757. -/
theorem noS6A_Law3757 : ∀ v : Magma.tupS6A,
    ¬ @Equation3757 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3757) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3757) (by native_decide) v.1 v.2
    ((@Law3757.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3760 takes them (134 nodes). -/
def ordS6A_Law3760 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3760. -/
theorem noS6A_Law3760 : ∀ v : Magma.tupS6A,
    ¬ @Equation3760 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3760) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3760) (by native_decide) v.1 v.2
    ((@Law3760.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3762 takes them (389 nodes). -/
def ordS6A_Law3762 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3762. -/
theorem noS6A_Law3762 : ∀ v : Magma.tupS6A,
    ¬ @Equation3762 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3762) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3762) (by native_decide) v.1 v.2
    ((@Law3762.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3763 takes them (143 nodes). -/
def ordS6A_Law3763 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3763. -/
theorem noS6A_Law3763 : ∀ v : Magma.tupS6A,
    ¬ @Equation3763 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3763) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3763) (by native_decide) v.1 v.2
    ((@Law3763.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3764 takes them (165 nodes). -/
def ordS6A_Law3764 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3764. -/
theorem noS6A_Law3764 : ∀ v : Magma.tupS6A,
    ¬ @Equation3764 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3764) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3764) (by native_decide) v.1 v.2
    ((@Law3764.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3765 takes them (281 nodes). -/
def ordS6A_Law3765 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3765. -/
theorem noS6A_Law3765 : ∀ v : Magma.tupS6A,
    ¬ @Equation3765 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3765) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3765) (by native_decide) v.1 v.2
    ((@Law3765.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3766 takes them (297 nodes). -/
def ordS6A_Law3766 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3766. -/
theorem noS6A_Law3766 : ∀ v : Magma.tupS6A,
    ¬ @Equation3766 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3766) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3766) (by native_decide) v.1 v.2
    ((@Law3766.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3767 takes them (134 nodes). -/
def ordS6A_Law3767 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3767. -/
theorem noS6A_Law3767 : ∀ v : Magma.tupS6A,
    ¬ @Equation3767 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3767) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3767) (by native_decide) v.1 v.2
    ((@Law3767.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3768 takes them (127 nodes). -/
def ordS6A_Law3768 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3768. -/
theorem noS6A_Law3768 : ∀ v : Magma.tupS6A,
    ¬ @Equation3768 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3768) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3768) (by native_decide) v.1 v.2
    ((@Law3768.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3770 takes them (120 nodes). -/
def ordS6A_Law3770 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3770. -/
theorem noS6A_Law3770 : ∀ v : Magma.tupS6A,
    ¬ @Equation3770 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3770) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3770) (by native_decide) v.1 v.2
    ((@Law3770.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3771 takes them (48 nodes). -/
def ordS6A_Law3771 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3771. -/
theorem noS6A_Law3771 : ∀ v : Magma.tupS6A,
    ¬ @Equation3771 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3771) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3771) (by native_decide) v.1 v.2
    ((@Law3771.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3772 takes them (101 nodes). -/
def ordS6A_Law3772 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3772. -/
theorem noS6A_Law3772 : ∀ v : Magma.tupS6A,
    ¬ @Equation3772 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3772) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3772) (by native_decide) v.1 v.2
    ((@Law3772.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3773 takes them (196 nodes). -/
def ordS6A_Law3773 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3773. -/
theorem noS6A_Law3773 : ∀ v : Magma.tupS6A,
    ¬ @Equation3773 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3773) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3773) (by native_decide) v.1 v.2
    ((@Law3773.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3774 takes them (84 nodes). -/
def ordS6A_Law3774 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3774. -/
theorem noS6A_Law3774 : ∀ v : Magma.tupS6A,
    ¬ @Equation3774 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3774) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3774) (by native_decide) v.1 v.2
    ((@Law3774.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3775 takes them (51 nodes). -/
def ordS6A_Law3775 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3775. -/
theorem noS6A_Law3775 : ∀ v : Magma.tupS6A,
    ¬ @Equation3775 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3775) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3775) (by native_decide) v.1 v.2
    ((@Law3775.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `20` equations. -/
theorem srch6A_refutes_39 :
    FamilyRefutes Magma.srch6A [
      3747, 3750, 3753, 3754, 3755, 3757, 3760, 3762, 3763, 3764, 3765, 3766, 3767, 3768, 3770,
      3771, 3772, 3773, 3774, 3775
    ] :=
  ⟨noS6A_Law3747, noS6A_Law3750, noS6A_Law3753, noS6A_Law3754, noS6A_Law3755, noS6A_Law3757, noS6A_Law3760, noS6A_Law3762, noS6A_Law3763, noS6A_Law3764, noS6A_Law3765, noS6A_Law3766, noS6A_Law3767, noS6A_Law3768, noS6A_Law3770, noS6A_Law3771, noS6A_Law3772, noS6A_Law3773, noS6A_Law3774, noS6A_Law3775⟩
