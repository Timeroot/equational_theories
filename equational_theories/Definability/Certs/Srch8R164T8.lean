import equational_theories.Definability.Srch_S8R164

/-!
# Structural certificate targets: `Magma.srch8R164` (part 9 of 18)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R164_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `84` equations here, 611 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R164_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3765 takes them (10 nodes). -/
def ordS8R164_Law3765 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3765. -/
theorem noS8R164_Law3765 : ∀ v : Magma.tup8R164,
    ¬ @Equation3765 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3765) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3765) (by native_decide) v.1 v.2
    ((@Law3765.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3766 takes them (8 nodes). -/
def ordS8R164_Law3766 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3766. -/
theorem noS8R164_Law3766 : ∀ v : Magma.tup8R164,
    ¬ @Equation3766 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3766) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3766) (by native_decide) v.1 v.2
    ((@Law3766.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3767 takes them (6 nodes). -/
def ordS8R164_Law3767 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3767. -/
theorem noS8R164_Law3767 : ∀ v : Magma.tup8R164,
    ¬ @Equation3767 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3767) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3767) (by native_decide) v.1 v.2
    ((@Law3767.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3768 takes them (7 nodes). -/
def ordS8R164_Law3768 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3768. -/
theorem noS8R164_Law3768 : ∀ v : Magma.tup8R164,
    ¬ @Equation3768 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3768) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3768) (by native_decide) v.1 v.2
    ((@Law3768.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3769 takes them (14 nodes). -/
def ordS8R164_Law3769 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3769. -/
theorem noS8R164_Law3769 : ∀ v : Magma.tup8R164,
    ¬ @Equation3769 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3769) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3769) (by native_decide) v.1 v.2
    ((@Law3769.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3771 takes them (6 nodes). -/
def ordS8R164_Law3771 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3771. -/
theorem noS8R164_Law3771 : ∀ v : Magma.tup8R164,
    ¬ @Equation3771 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3771) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3771) (by native_decide) v.1 v.2
    ((@Law3771.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3772 takes them (7 nodes). -/
def ordS8R164_Law3772 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3772. -/
theorem noS8R164_Law3772 : ∀ v : Magma.tup8R164,
    ¬ @Equation3772 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3772) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3772) (by native_decide) v.1 v.2
    ((@Law3772.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3773 takes them (10 nodes). -/
def ordS8R164_Law3773 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3773. -/
theorem noS8R164_Law3773 : ∀ v : Magma.tup8R164,
    ¬ @Equation3773 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3773) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3773) (by native_decide) v.1 v.2
    ((@Law3773.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3774 takes them (7 nodes). -/
def ordS8R164_Law3774 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3774. -/
theorem noS8R164_Law3774 : ∀ v : Magma.tup8R164,
    ¬ @Equation3774 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3774) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3774) (by native_decide) v.1 v.2
    ((@Law3774.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3775 takes them (6 nodes). -/
def ordS8R164_Law3775 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3775. -/
theorem noS8R164_Law3775 : ∀ v : Magma.tup8R164,
    ¬ @Equation3775 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3775) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3775) (by native_decide) v.1 v.2
    ((@Law3775.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3777 takes them (10 nodes). -/
def ordS8R164_Law3777 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3777. -/
theorem noS8R164_Law3777 : ∀ v : Magma.tup8R164,
    ¬ @Equation3777 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3777) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3777) (by native_decide) v.1 v.2
    ((@Law3777.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3778 takes them (7 nodes). -/
def ordS8R164_Law3778 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3778. -/
theorem noS8R164_Law3778 : ∀ v : Magma.tup8R164,
    ¬ @Equation3778 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3778) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3778) (by native_decide) v.1 v.2
    ((@Law3778.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3779 takes them (6 nodes). -/
def ordS8R164_Law3779 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3779. -/
theorem noS8R164_Law3779 : ∀ v : Magma.tup8R164,
    ¬ @Equation3779 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3779) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3779) (by native_decide) v.1 v.2
    ((@Law3779.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3780 takes them (7 nodes). -/
def ordS8R164_Law3780 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3780. -/
theorem noS8R164_Law3780 : ∀ v : Magma.tup8R164,
    ¬ @Equation3780 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3780) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3780) (by native_decide) v.1 v.2
    ((@Law3780.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3781 takes them (10 nodes). -/
def ordS8R164_Law3781 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3781. -/
theorem noS8R164_Law3781 : ∀ v : Magma.tup8R164,
    ¬ @Equation3781 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3781) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3781) (by native_decide) v.1 v.2
    ((@Law3781.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3782 takes them (7 nodes). -/
def ordS8R164_Law3782 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3782. -/
theorem noS8R164_Law3782 : ∀ v : Magma.tup8R164,
    ¬ @Equation3782 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3782) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3782) (by native_decide) v.1 v.2
    ((@Law3782.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3783 takes them (7 nodes). -/
def ordS8R164_Law3783 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3783. -/
theorem noS8R164_Law3783 : ∀ v : Magma.tup8R164,
    ¬ @Equation3783 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3783) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3783) (by native_decide) v.1 v.2
    ((@Law3783.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3784 takes them (6 nodes). -/
def ordS8R164_Law3784 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3784. -/
theorem noS8R164_Law3784 : ∀ v : Magma.tup8R164,
    ¬ @Equation3784 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3784) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3784) (by native_decide) v.1 v.2
    ((@Law3784.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3785 takes them (6 nodes). -/
def ordS8R164_Law3785 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3785. -/
theorem noS8R164_Law3785 : ∀ v : Magma.tup8R164,
    ¬ @Equation3785 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3785) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3785) (by native_decide) v.1 v.2
    ((@Law3785.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3786 takes them (14 nodes). -/
def ordS8R164_Law3786 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3786. -/
theorem noS8R164_Law3786 : ∀ v : Magma.tup8R164,
    ¬ @Equation3786 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3786) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3786) (by native_decide) v.1 v.2
    ((@Law3786.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3787 takes them (6 nodes). -/
def ordS8R164_Law3787 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3787. -/
theorem noS8R164_Law3787 : ∀ v : Magma.tup8R164,
    ¬ @Equation3787 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3787) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3787) (by native_decide) v.1 v.2
    ((@Law3787.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3788 takes them (6 nodes). -/
def ordS8R164_Law3788 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3788. -/
theorem noS8R164_Law3788 : ∀ v : Magma.tup8R164,
    ¬ @Equation3788 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3788) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3788) (by native_decide) v.1 v.2
    ((@Law3788.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3789 takes them (7 nodes). -/
def ordS8R164_Law3789 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3789. -/
theorem noS8R164_Law3789 : ∀ v : Magma.tup8R164,
    ¬ @Equation3789 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3789) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3789) (by native_decide) v.1 v.2
    ((@Law3789.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3790 takes them (10 nodes). -/
def ordS8R164_Law3790 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3790. -/
theorem noS8R164_Law3790 : ∀ v : Magma.tup8R164,
    ¬ @Equation3790 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3790) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3790) (by native_decide) v.1 v.2
    ((@Law3790.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3792 takes them (6 nodes). -/
def ordS8R164_Law3792 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3792. -/
theorem noS8R164_Law3792 : ∀ v : Magma.tup8R164,
    ¬ @Equation3792 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3792) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3792) (by native_decide) v.1 v.2
    ((@Law3792.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3793 takes them (6 nodes). -/
def ordS8R164_Law3793 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3793. -/
theorem noS8R164_Law3793 : ∀ v : Magma.tup8R164,
    ¬ @Equation3793 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3793) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3793) (by native_decide) v.1 v.2
    ((@Law3793.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3795 takes them (6 nodes). -/
def ordS8R164_Law3795 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3795. -/
theorem noS8R164_Law3795 : ∀ v : Magma.tup8R164,
    ¬ @Equation3795 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3795) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3795) (by native_decide) v.1 v.2
    ((@Law3795.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3796 takes them (6 nodes). -/
def ordS8R164_Law3796 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3796. -/
theorem noS8R164_Law3796 : ∀ v : Magma.tup8R164,
    ¬ @Equation3796 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3796) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3796) (by native_decide) v.1 v.2
    ((@Law3796.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3797 takes them (6 nodes). -/
def ordS8R164_Law3797 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3797. -/
theorem noS8R164_Law3797 : ∀ v : Magma.tup8R164,
    ¬ @Equation3797 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3797) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3797) (by native_decide) v.1 v.2
    ((@Law3797.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3798 takes them (10 nodes). -/
def ordS8R164_Law3798 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3798. -/
theorem noS8R164_Law3798 : ∀ v : Magma.tup8R164,
    ¬ @Equation3798 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3798) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3798) (by native_decide) v.1 v.2
    ((@Law3798.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3799 takes them (6 nodes). -/
def ordS8R164_Law3799 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3799. -/
theorem noS8R164_Law3799 : ∀ v : Magma.tup8R164,
    ¬ @Equation3799 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3799) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3799) (by native_decide) v.1 v.2
    ((@Law3799.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3800 takes them (6 nodes). -/
def ordS8R164_Law3800 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3800. -/
theorem noS8R164_Law3800 : ∀ v : Magma.tup8R164,
    ¬ @Equation3800 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3800) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3800) (by native_decide) v.1 v.2
    ((@Law3800.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3801 takes them (6 nodes). -/
def ordS8R164_Law3801 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3801. -/
theorem noS8R164_Law3801 : ∀ v : Magma.tup8R164,
    ¬ @Equation3801 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3801) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3801) (by native_decide) v.1 v.2
    ((@Law3801.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3802 takes them (7 nodes). -/
def ordS8R164_Law3802 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3802. -/
theorem noS8R164_Law3802 : ∀ v : Magma.tup8R164,
    ¬ @Equation3802 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3802) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3802) (by native_decide) v.1 v.2
    ((@Law3802.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3803 takes them (11 nodes). -/
def ordS8R164_Law3803 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3803. -/
theorem noS8R164_Law3803 : ∀ v : Magma.tup8R164,
    ¬ @Equation3803 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3803) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3803) (by native_decide) v.1 v.2
    ((@Law3803.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3805 takes them (6 nodes). -/
def ordS8R164_Law3805 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3805. -/
theorem noS8R164_Law3805 : ∀ v : Magma.tup8R164,
    ¬ @Equation3805 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3805) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3805) (by native_decide) v.1 v.2
    ((@Law3805.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3806 takes them (7 nodes). -/
def ordS8R164_Law3806 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3806. -/
theorem noS8R164_Law3806 : ∀ v : Magma.tup8R164,
    ¬ @Equation3806 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3806) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3806) (by native_decide) v.1 v.2
    ((@Law3806.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3807 takes them (10 nodes). -/
def ordS8R164_Law3807 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3807. -/
theorem noS8R164_Law3807 : ∀ v : Magma.tup8R164,
    ¬ @Equation3807 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3807) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3807) (by native_decide) v.1 v.2
    ((@Law3807.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3808 takes them (7 nodes). -/
def ordS8R164_Law3808 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3808. -/
theorem noS8R164_Law3808 : ∀ v : Magma.tup8R164,
    ¬ @Equation3808 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3808) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3808) (by native_decide) v.1 v.2
    ((@Law3808.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3809 takes them (6 nodes). -/
def ordS8R164_Law3809 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3809. -/
theorem noS8R164_Law3809 : ∀ v : Magma.tup8R164,
    ¬ @Equation3809 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3809) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3809) (by native_decide) v.1 v.2
    ((@Law3809.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3811 takes them (10 nodes). -/
def ordS8R164_Law3811 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3811. -/
theorem noS8R164_Law3811 : ∀ v : Magma.tup8R164,
    ¬ @Equation3811 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3811) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3811) (by native_decide) v.1 v.2
    ((@Law3811.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3812 takes them (7 nodes). -/
def ordS8R164_Law3812 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3812. -/
theorem noS8R164_Law3812 : ∀ v : Magma.tup8R164,
    ¬ @Equation3812 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3812) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3812) (by native_decide) v.1 v.2
    ((@Law3812.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3813 takes them (6 nodes). -/
def ordS8R164_Law3813 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3813. -/
theorem noS8R164_Law3813 : ∀ v : Magma.tup8R164,
    ¬ @Equation3813 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3813) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3813) (by native_decide) v.1 v.2
    ((@Law3813.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3814 takes them (7 nodes). -/
def ordS8R164_Law3814 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3814. -/
theorem noS8R164_Law3814 : ∀ v : Magma.tup8R164,
    ¬ @Equation3814 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3814) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3814) (by native_decide) v.1 v.2
    ((@Law3814.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3815 takes them (10 nodes). -/
def ordS8R164_Law3815 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3815. -/
theorem noS8R164_Law3815 : ∀ v : Magma.tup8R164,
    ¬ @Equation3815 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3815) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3815) (by native_decide) v.1 v.2
    ((@Law3815.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3816 takes them (7 nodes). -/
def ordS8R164_Law3816 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3816. -/
theorem noS8R164_Law3816 : ∀ v : Magma.tup8R164,
    ¬ @Equation3816 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3816) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3816) (by native_decide) v.1 v.2
    ((@Law3816.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3817 takes them (7 nodes). -/
def ordS8R164_Law3817 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3817. -/
theorem noS8R164_Law3817 : ∀ v : Magma.tup8R164,
    ¬ @Equation3817 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3817) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3817) (by native_decide) v.1 v.2
    ((@Law3817.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3818 takes them (6 nodes). -/
def ordS8R164_Law3818 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3818. -/
theorem noS8R164_Law3818 : ∀ v : Magma.tup8R164,
    ¬ @Equation3818 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3818) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3818) (by native_decide) v.1 v.2
    ((@Law3818.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3819 takes them (7 nodes). -/
def ordS8R164_Law3819 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3819. -/
theorem noS8R164_Law3819 : ∀ v : Magma.tup8R164,
    ¬ @Equation3819 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3819) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3819) (by native_decide) v.1 v.2
    ((@Law3819.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3821 takes them (6 nodes). -/
def ordS8R164_Law3821 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3821. -/
theorem noS8R164_Law3821 : ∀ v : Magma.tup8R164,
    ¬ @Equation3821 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3821) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3821) (by native_decide) v.1 v.2
    ((@Law3821.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3822 takes them (6 nodes). -/
def ordS8R164_Law3822 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3822. -/
theorem noS8R164_Law3822 : ∀ v : Magma.tup8R164,
    ¬ @Equation3822 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3822) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3822) (by native_decide) v.1 v.2
    ((@Law3822.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3824 takes them (10 nodes). -/
def ordS8R164_Law3824 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3824. -/
theorem noS8R164_Law3824 : ∀ v : Magma.tup8R164,
    ¬ @Equation3824 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3824) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3824) (by native_decide) v.1 v.2
    ((@Law3824.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3825 takes them (7 nodes). -/
def ordS8R164_Law3825 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3825. -/
theorem noS8R164_Law3825 : ∀ v : Magma.tup8R164,
    ¬ @Equation3825 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3825) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3825) (by native_decide) v.1 v.2
    ((@Law3825.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3826 takes them (6 nodes). -/
def ordS8R164_Law3826 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3826. -/
theorem noS8R164_Law3826 : ∀ v : Magma.tup8R164,
    ¬ @Equation3826 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3826) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3826) (by native_decide) v.1 v.2
    ((@Law3826.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3827 takes them (6 nodes). -/
def ordS8R164_Law3827 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3827. -/
theorem noS8R164_Law3827 : ∀ v : Magma.tup8R164,
    ¬ @Equation3827 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3827) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3827) (by native_decide) v.1 v.2
    ((@Law3827.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3828 takes them (10 nodes). -/
def ordS8R164_Law3828 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3828. -/
theorem noS8R164_Law3828 : ∀ v : Magma.tup8R164,
    ¬ @Equation3828 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3828) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3828) (by native_decide) v.1 v.2
    ((@Law3828.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3829 takes them (6 nodes). -/
def ordS8R164_Law3829 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3829. -/
theorem noS8R164_Law3829 : ∀ v : Magma.tup8R164,
    ¬ @Equation3829 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3829) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 3)
    (ord := ordS8R164_Law3829) (by native_decide) v.1 v.2
    ((@Law3829.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3830 takes them (6 nodes). -/
def ordS8R164_Law3830 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3830. -/
theorem noS8R164_Law3830 : ∀ v : Magma.tup8R164,
    ¬ @Equation3830 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3830) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3830) (by native_decide) v.1 v.2
    ((@Law3830.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3831 takes them (6 nodes). -/
def ordS8R164_Law3831 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3831. -/
theorem noS8R164_Law3831 : ∀ v : Magma.tup8R164,
    ¬ @Equation3831 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3831) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3831) (by native_decide) v.1 v.2
    ((@Law3831.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3832 takes them (10 nodes). -/
def ordS8R164_Law3832 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3832. -/
theorem noS8R164_Law3832 : ∀ v : Magma.tup8R164,
    ¬ @Equation3832 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3832) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3832) (by native_decide) v.1 v.2
    ((@Law3832.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3833 takes them (6 nodes). -/
def ordS8R164_Law3833 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3833. -/
theorem noS8R164_Law3833 : ∀ v : Magma.tup8R164,
    ¬ @Equation3833 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3833) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3833) (by native_decide) v.1 v.2
    ((@Law3833.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3834 takes them (6 nodes). -/
def ordS8R164_Law3834 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3834. -/
theorem noS8R164_Law3834 : ∀ v : Magma.tup8R164,
    ¬ @Equation3834 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3834) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3834) (by native_decide) v.1 v.2
    ((@Law3834.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3835 takes them (6 nodes). -/
def ordS8R164_Law3835 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3835. -/
theorem noS8R164_Law3835 : ∀ v : Magma.tup8R164,
    ¬ @Equation3835 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3835) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3835) (by native_decide) v.1 v.2
    ((@Law3835.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3836 takes them (6 nodes). -/
def ordS8R164_Law3836 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3836. -/
theorem noS8R164_Law3836 : ∀ v : Magma.tup8R164,
    ¬ @Equation3836 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3836) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3836) (by native_decide) v.1 v.2
    ((@Law3836.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3837 takes them (10 nodes). -/
def ordS8R164_Law3837 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3837. -/
theorem noS8R164_Law3837 : ∀ v : Magma.tup8R164,
    ¬ @Equation3837 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3837) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3837) (by native_decide) v.1 v.2
    ((@Law3837.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3838 takes them (6 nodes). -/
def ordS8R164_Law3838 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3838. -/
theorem noS8R164_Law3838 : ∀ v : Magma.tup8R164,
    ¬ @Equation3838 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3838) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3838) (by native_decide) v.1 v.2
    ((@Law3838.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3839 takes them (6 nodes). -/
def ordS8R164_Law3839 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3839. -/
theorem noS8R164_Law3839 : ∀ v : Magma.tup8R164,
    ¬ @Equation3839 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3839) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3839) (by native_decide) v.1 v.2
    ((@Law3839.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3840 takes them (6 nodes). -/
def ordS8R164_Law3840 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3840. -/
theorem noS8R164_Law3840 : ∀ v : Magma.tup8R164,
    ¬ @Equation3840 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3840) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3840) (by native_decide) v.1 v.2
    ((@Law3840.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3841 takes them (7 nodes). -/
def ordS8R164_Law3841 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3841. -/
theorem noS8R164_Law3841 : ∀ v : Magma.tup8R164,
    ¬ @Equation3841 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3841) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3841) (by native_decide) v.1 v.2
    ((@Law3841.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3842 takes them (10 nodes). -/
def ordS8R164_Law3842 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3842. -/
theorem noS8R164_Law3842 : ∀ v : Magma.tup8R164,
    ¬ @Equation3842 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3842) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3842) (by native_decide) v.1 v.2
    ((@Law3842.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3843 takes them (7 nodes). -/
def ordS8R164_Law3843 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3843. -/
theorem noS8R164_Law3843 : ∀ v : Magma.tup8R164,
    ¬ @Equation3843 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3843) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3843) (by native_decide) v.1 v.2
    ((@Law3843.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3844 takes them (7 nodes). -/
def ordS8R164_Law3844 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3844. -/
theorem noS8R164_Law3844 : ∀ v : Magma.tup8R164,
    ¬ @Equation3844 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3844) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3844) (by native_decide) v.1 v.2
    ((@Law3844.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3845 takes them (6 nodes). -/
def ordS8R164_Law3845 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3845. -/
theorem noS8R164_Law3845 : ∀ v : Magma.tup8R164,
    ¬ @Equation3845 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3845) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3845) (by native_decide) v.1 v.2
    ((@Law3845.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3846 takes them (6 nodes). -/
def ordS8R164_Law3846 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3846. -/
theorem noS8R164_Law3846 : ∀ v : Magma.tup8R164,
    ¬ @Equation3846 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3846) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3846) (by native_decide) v.1 v.2
    ((@Law3846.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3847 takes them (10 nodes). -/
def ordS8R164_Law3847 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3847. -/
theorem noS8R164_Law3847 : ∀ v : Magma.tup8R164,
    ¬ @Equation3847 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3847) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3847) (by native_decide) v.1 v.2
    ((@Law3847.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3848 takes them (6 nodes). -/
def ordS8R164_Law3848 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3848. -/
theorem noS8R164_Law3848 : ∀ v : Magma.tup8R164,
    ¬ @Equation3848 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3848) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3848) (by native_decide) v.1 v.2
    ((@Law3848.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3849 takes them (6 nodes). -/
def ordS8R164_Law3849 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3849. -/
theorem noS8R164_Law3849 : ∀ v : Magma.tup8R164,
    ¬ @Equation3849 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3849) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3849) (by native_decide) v.1 v.2
    ((@Law3849.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3850 takes them (6 nodes). -/
def ordS8R164_Law3850 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3850. -/
theorem noS8R164_Law3850 : ∀ v : Magma.tup8R164,
    ¬ @Equation3850 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3850) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3850) (by native_decide) v.1 v.2
    ((@Law3850.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3851 takes them (6 nodes). -/
def ordS8R164_Law3851 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3851. -/
theorem noS8R164_Law3851 : ∀ v : Magma.tup8R164,
    ¬ @Equation3851 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3851) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3851) (by native_decide) v.1 v.2
    ((@Law3851.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3852 takes them (10 nodes). -/
def ordS8R164_Law3852 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3852. -/
theorem noS8R164_Law3852 : ∀ v : Magma.tup8R164,
    ¬ @Equation3852 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3852) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3852) (by native_decide) v.1 v.2
    ((@Law3852.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3853 takes them (6 nodes). -/
def ordS8R164_Law3853 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3853. -/
theorem noS8R164_Law3853 : ∀ v : Magma.tup8R164,
    ¬ @Equation3853 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3853) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3853) (by native_decide) v.1 v.2
    ((@Law3853.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3854 takes them (6 nodes). -/
def ordS8R164_Law3854 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3854. -/
theorem noS8R164_Law3854 : ∀ v : Magma.tup8R164,
    ¬ @Equation3854 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3854) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 4)
    (ord := ordS8R164_Law3854) (by native_decide) v.1 v.2
    ((@Law3854.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3855 takes them (6 nodes). -/
def ordS8R164_Law3855 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3855. -/
theorem noS8R164_Law3855 : ∀ v : Magma.tup8R164,
    ¬ @Equation3855 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3855) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3855) (by native_decide) v.1 v.2
    ((@Law3855.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3856 takes them (6 nodes). -/
def ordS8R164_Law3856 : List (Fin 5) := [0, 1, 2, 3, 4]

/-- No member of the class satisfies equation 3856. -/
theorem noS8R164_Law3856 : ∀ v : Magma.tup8R164,
    ¬ @Equation3856 (Fin 8) (Magma.srch8R164 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3856) (E := S8R164.E) (tr := S8R164.tr) (z := S8R164.z)
    (st := S8R164.st) (X := S8R164.X) (envs := Magma.envsRed 8 S8R164.E 5)
    (ord := ordS8R164_Law3856) (by native_decide) v.1 v.2
    ((@Law3856.models_iff (Fin 8) (Magma.srch8R164 v)).mpr hv)

/-- No member of the class satisfies any of these `84` equations. -/
theorem srch8R164_refutes_8 :
    FamilyRefutes Magma.srch8R164 [
      3765, 3766, 3767, 3768, 3769, 3771, 3772, 3773, 3774, 3775, 3777, 3778, 3779, 3780, 3781,
      3782, 3783, 3784, 3785, 3786, 3787, 3788, 3789, 3790, 3792, 3793, 3795, 3796, 3797, 3798,
      3799, 3800, 3801, 3802, 3803, 3805, 3806, 3807, 3808, 3809, 3811, 3812, 3813, 3814, 3815,
      3816, 3817, 3818, 3819, 3821, 3822, 3824, 3825, 3826, 3827, 3828, 3829, 3830, 3831, 3832,
      3833, 3834, 3835, 3836, 3837, 3838, 3839, 3840, 3841, 3842, 3843, 3844, 3845, 3846, 3847,
      3848, 3849, 3850, 3851, 3852, 3853, 3854, 3855, 3856
    ] :=
  ⟨noS8R164_Law3765, noS8R164_Law3766, noS8R164_Law3767, noS8R164_Law3768, noS8R164_Law3769, noS8R164_Law3771, noS8R164_Law3772, noS8R164_Law3773, noS8R164_Law3774, noS8R164_Law3775, noS8R164_Law3777, noS8R164_Law3778, noS8R164_Law3779, noS8R164_Law3780, noS8R164_Law3781, noS8R164_Law3782, noS8R164_Law3783, noS8R164_Law3784, noS8R164_Law3785, noS8R164_Law3786, noS8R164_Law3787, noS8R164_Law3788, noS8R164_Law3789, noS8R164_Law3790, noS8R164_Law3792, noS8R164_Law3793, noS8R164_Law3795, noS8R164_Law3796, noS8R164_Law3797, noS8R164_Law3798, noS8R164_Law3799, noS8R164_Law3800, noS8R164_Law3801, noS8R164_Law3802, noS8R164_Law3803, noS8R164_Law3805, noS8R164_Law3806, noS8R164_Law3807, noS8R164_Law3808, noS8R164_Law3809, noS8R164_Law3811, noS8R164_Law3812, noS8R164_Law3813, noS8R164_Law3814, noS8R164_Law3815, noS8R164_Law3816, noS8R164_Law3817, noS8R164_Law3818, noS8R164_Law3819, noS8R164_Law3821, noS8R164_Law3822, noS8R164_Law3824, noS8R164_Law3825, noS8R164_Law3826, noS8R164_Law3827, noS8R164_Law3828, noS8R164_Law3829, noS8R164_Law3830, noS8R164_Law3831, noS8R164_Law3832, noS8R164_Law3833, noS8R164_Law3834, noS8R164_Law3835, noS8R164_Law3836, noS8R164_Law3837, noS8R164_Law3838, noS8R164_Law3839, noS8R164_Law3840, noS8R164_Law3841, noS8R164_Law3842, noS8R164_Law3843, noS8R164_Law3844, noS8R164_Law3845, noS8R164_Law3846, noS8R164_Law3847, noS8R164_Law3848, noS8R164_Law3849, noS8R164_Law3850, noS8R164_Law3851, noS8R164_Law3852, noS8R164_Law3853, noS8R164_Law3854, noS8R164_Law3855, noS8R164_Law3856⟩
