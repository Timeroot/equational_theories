import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 41 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `29`
equations here, 2,828 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3776 takes them (165 nodes). -/
def ordS6A_Law3776 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3776. -/
theorem noS6A_Law3776 : ∀ v : Magma.tupS6A,
    ¬ @Equation3776 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3776) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3776) (by native_decide) v.1 v.2
    ((@Law3776.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3777 takes them (151 nodes). -/
def ordS6A_Law3777 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3777. -/
theorem noS6A_Law3777 : ∀ v : Magma.tupS6A,
    ¬ @Equation3777 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3777) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3777) (by native_decide) v.1 v.2
    ((@Law3777.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3778 takes them (131 nodes). -/
def ordS6A_Law3778 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3778. -/
theorem noS6A_Law3778 : ∀ v : Magma.tupS6A,
    ¬ @Equation3778 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3778) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3778) (by native_decide) v.1 v.2
    ((@Law3778.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3779 takes them (76 nodes). -/
def ordS6A_Law3779 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3779. -/
theorem noS6A_Law3779 : ∀ v : Magma.tupS6A,
    ¬ @Equation3779 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3779) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3779) (by native_decide) v.1 v.2
    ((@Law3779.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3780 takes them (61 nodes). -/
def ordS6A_Law3780 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3780. -/
theorem noS6A_Law3780 : ∀ v : Magma.tupS6A,
    ¬ @Equation3780 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3780) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3780) (by native_decide) v.1 v.2
    ((@Law3780.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3781 takes them (117 nodes). -/
def ordS6A_Law3781 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3781. -/
theorem noS6A_Law3781 : ∀ v : Magma.tupS6A,
    ¬ @Equation3781 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3781) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3781) (by native_decide) v.1 v.2
    ((@Law3781.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3782 takes them (67 nodes). -/
def ordS6A_Law3782 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3782. -/
theorem noS6A_Law3782 : ∀ v : Magma.tupS6A,
    ¬ @Equation3782 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3782) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3782) (by native_decide) v.1 v.2
    ((@Law3782.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3783 takes them (70 nodes). -/
def ordS6A_Law3783 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3783. -/
theorem noS6A_Law3783 : ∀ v : Magma.tupS6A,
    ¬ @Equation3783 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3783) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3783) (by native_decide) v.1 v.2
    ((@Law3783.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3784 takes them (48 nodes). -/
def ordS6A_Law3784 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3784. -/
theorem noS6A_Law3784 : ∀ v : Magma.tupS6A,
    ¬ @Equation3784 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3784) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3784) (by native_decide) v.1 v.2
    ((@Law3784.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3785 takes them (101 nodes). -/
def ordS6A_Law3785 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3785. -/
theorem noS6A_Law3785 : ∀ v : Magma.tupS6A,
    ¬ @Equation3785 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3785) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3785) (by native_decide) v.1 v.2
    ((@Law3785.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3787 takes them (72 nodes). -/
def ordS6A_Law3787 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3787. -/
theorem noS6A_Law3787 : ∀ v : Magma.tupS6A,
    ¬ @Equation3787 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3787) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3787) (by native_decide) v.1 v.2
    ((@Law3787.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3788 takes them (63 nodes). -/
def ordS6A_Law3788 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3788. -/
theorem noS6A_Law3788 : ∀ v : Magma.tupS6A,
    ¬ @Equation3788 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3788) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3788) (by native_decide) v.1 v.2
    ((@Law3788.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3789 takes them (152 nodes). -/
def ordS6A_Law3789 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3789. -/
theorem noS6A_Law3789 : ∀ v : Magma.tupS6A,
    ¬ @Equation3789 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3789) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3789) (by native_decide) v.1 v.2
    ((@Law3789.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3791 takes them (171 nodes). -/
def ordS6A_Law3791 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3791. -/
theorem noS6A_Law3791 : ∀ v : Magma.tupS6A,
    ¬ @Equation3791 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3791) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3791) (by native_decide) v.1 v.2
    ((@Law3791.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3792 takes them (78 nodes). -/
def ordS6A_Law3792 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3792. -/
theorem noS6A_Law3792 : ∀ v : Magma.tupS6A,
    ¬ @Equation3792 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3792) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3792) (by native_decide) v.1 v.2
    ((@Law3792.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3793 takes them (91 nodes). -/
def ordS6A_Law3793 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3793. -/
theorem noS6A_Law3793 : ∀ v : Magma.tupS6A,
    ¬ @Equation3793 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3793) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3793) (by native_decide) v.1 v.2
    ((@Law3793.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3795 takes them (90 nodes). -/
def ordS6A_Law3795 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3795. -/
theorem noS6A_Law3795 : ∀ v : Magma.tupS6A,
    ¬ @Equation3795 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3795) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3795) (by native_decide) v.1 v.2
    ((@Law3795.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3796 takes them (64 nodes). -/
def ordS6A_Law3796 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3796. -/
theorem noS6A_Law3796 : ∀ v : Magma.tupS6A,
    ¬ @Equation3796 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3796) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3796) (by native_decide) v.1 v.2
    ((@Law3796.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3797 takes them (78 nodes). -/
def ordS6A_Law3797 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3797. -/
theorem noS6A_Law3797 : ∀ v : Magma.tupS6A,
    ¬ @Equation3797 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3797) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3797) (by native_decide) v.1 v.2
    ((@Law3797.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3798 takes them (91 nodes). -/
def ordS6A_Law3798 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3798. -/
theorem noS6A_Law3798 : ∀ v : Magma.tupS6A,
    ¬ @Equation3798 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3798) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3798) (by native_decide) v.1 v.2
    ((@Law3798.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3799 takes them (72 nodes). -/
def ordS6A_Law3799 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3799. -/
theorem noS6A_Law3799 : ∀ v : Magma.tupS6A,
    ¬ @Equation3799 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3799) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3799) (by native_decide) v.1 v.2
    ((@Law3799.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3800 takes them (73 nodes). -/
def ordS6A_Law3800 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3800. -/
theorem noS6A_Law3800 : ∀ v : Magma.tupS6A,
    ¬ @Equation3800 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3800) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3800) (by native_decide) v.1 v.2
    ((@Law3800.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3801 takes them (63 nodes). -/
def ordS6A_Law3801 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3801. -/
theorem noS6A_Law3801 : ∀ v : Magma.tupS6A,
    ¬ @Equation3801 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3801) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3801) (by native_decide) v.1 v.2
    ((@Law3801.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3802 takes them (80 nodes). -/
def ordS6A_Law3802 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3802. -/
theorem noS6A_Law3802 : ∀ v : Magma.tupS6A,
    ¬ @Equation3802 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3802) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3802) (by native_decide) v.1 v.2
    ((@Law3802.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3804 takes them (87 nodes). -/
def ordS6A_Law3804 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3804. -/
theorem noS6A_Law3804 : ∀ v : Magma.tupS6A,
    ¬ @Equation3804 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3804) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3804) (by native_decide) v.1 v.2
    ((@Law3804.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3805 takes them (34 nodes). -/
def ordS6A_Law3805 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3805. -/
theorem noS6A_Law3805 : ∀ v : Magma.tupS6A,
    ¬ @Equation3805 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3805) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3805) (by native_decide) v.1 v.2
    ((@Law3805.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3806 takes them (146 nodes). -/
def ordS6A_Law3806 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3806. -/
theorem noS6A_Law3806 : ∀ v : Magma.tupS6A,
    ¬ @Equation3806 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3806) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3806) (by native_decide) v.1 v.2
    ((@Law3806.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3807 takes them (239 nodes). -/
def ordS6A_Law3807 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3807. -/
theorem noS6A_Law3807 : ∀ v : Magma.tupS6A,
    ¬ @Equation3807 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3807) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3807) (by native_decide) v.1 v.2
    ((@Law3807.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3808 takes them (97 nodes). -/
def ordS6A_Law3808 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3808. -/
theorem noS6A_Law3808 : ∀ v : Magma.tupS6A,
    ¬ @Equation3808 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3808) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3808) (by native_decide) v.1 v.2
    ((@Law3808.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `29` equations. -/
theorem srch6A_refutes_40 :
    FamilyRefutes Magma.srch6A [
      3776, 3777, 3778, 3779, 3780, 3781, 3782, 3783, 3784, 3785, 3787, 3788, 3789, 3791, 3792,
      3793, 3795, 3796, 3797, 3798, 3799, 3800, 3801, 3802, 3804, 3805, 3806, 3807, 3808
    ] :=
  ⟨noS6A_Law3776, noS6A_Law3777, noS6A_Law3778, noS6A_Law3779, noS6A_Law3780, noS6A_Law3781, noS6A_Law3782, noS6A_Law3783, noS6A_Law3784, noS6A_Law3785, noS6A_Law3787, noS6A_Law3788, noS6A_Law3789, noS6A_Law3791, noS6A_Law3792, noS6A_Law3793, noS6A_Law3795, noS6A_Law3796, noS6A_Law3797, noS6A_Law3798, noS6A_Law3799, noS6A_Law3800, noS6A_Law3801, noS6A_Law3802, noS6A_Law3804, noS6A_Law3805, noS6A_Law3806, noS6A_Law3807, noS6A_Law3808⟩
