import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 39 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `25`
equations here, 2,938 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3654 takes them (50 nodes). -/
def ordS6A_Law3654 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3654. -/
theorem noS6A_Law3654 : ∀ v : Magma.tupS6A,
    ¬ @Equation3654 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3654) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3654) (by native_decide) v.1 v.2
    ((@Law3654.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3655 takes them (22 nodes). -/
def ordS6A_Law3655 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3655. -/
theorem noS6A_Law3655 : ∀ v : Magma.tupS6A,
    ¬ @Equation3655 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3655) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3655) (by native_decide) v.1 v.2
    ((@Law3655.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3656 takes them (22 nodes). -/
def ordS6A_Law3656 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3656. -/
theorem noS6A_Law3656 : ∀ v : Magma.tupS6A,
    ¬ @Equation3656 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3656) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3656) (by native_decide) v.1 v.2
    ((@Law3656.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3657 takes them (22 nodes). -/
def ordS6A_Law3657 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3657. -/
theorem noS6A_Law3657 : ∀ v : Magma.tupS6A,
    ¬ @Equation3657 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3657) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law3657) (by native_decide) v.1 v.2
    ((@Law3657.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3658 takes them (22 nodes). -/
def ordS6A_Law3658 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3658. -/
theorem noS6A_Law3658 : ∀ v : Magma.tupS6A,
    ¬ @Equation3658 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3658) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 6)
    (ord := ordS6A_Law3658) (by native_decide) v.1 v.2
    ((@Law3658.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3711 takes them (298 nodes). -/
def ordS6A_Law3711 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3711. -/
theorem noS6A_Law3711 : ∀ v : Magma.tupS6A,
    ¬ @Equation3711 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3711) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law3711) (by native_decide) v.1 v.2
    ((@Law3711.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3713 takes them (172 nodes). -/
def ordS6A_Law3713 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3713. -/
theorem noS6A_Law3713 : ∀ v : Magma.tupS6A,
    ¬ @Equation3713 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3713) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3713) (by native_decide) v.1 v.2
    ((@Law3713.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3717 takes them (190 nodes). -/
def ordS6A_Law3717 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3717. -/
theorem noS6A_Law3717 : ∀ v : Magma.tupS6A,
    ¬ @Equation3717 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3717) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3717) (by native_decide) v.1 v.2
    ((@Law3717.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3718 takes them (222 nodes). -/
def ordS6A_Law3718 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3718. -/
theorem noS6A_Law3718 : ∀ v : Magma.tupS6A,
    ¬ @Equation3718 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3718) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3718) (by native_decide) v.1 v.2
    ((@Law3718.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3719 takes them (298 nodes). -/
def ordS6A_Law3719 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3719. -/
theorem noS6A_Law3719 : ∀ v : Magma.tupS6A,
    ¬ @Equation3719 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3719) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3719) (by native_decide) v.1 v.2
    ((@Law3719.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3720 takes them (163 nodes). -/
def ordS6A_Law3720 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3720. -/
theorem noS6A_Law3720 : ∀ v : Magma.tupS6A,
    ¬ @Equation3720 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3720) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3720) (by native_decide) v.1 v.2
    ((@Law3720.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3731 takes them (99 nodes). -/
def ordS6A_Law3731 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3731. -/
theorem noS6A_Law3731 : ∀ v : Magma.tupS6A,
    ¬ @Equation3731 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3731) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3731) (by native_decide) v.1 v.2
    ((@Law3731.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3733 takes them (57 nodes). -/
def ordS6A_Law3733 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3733. -/
theorem noS6A_Law3733 : ∀ v : Magma.tupS6A,
    ¬ @Equation3733 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3733) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3733) (by native_decide) v.1 v.2
    ((@Law3733.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3734 takes them (57 nodes). -/
def ordS6A_Law3734 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3734. -/
theorem noS6A_Law3734 : ∀ v : Magma.tupS6A,
    ¬ @Equation3734 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3734) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3734) (by native_decide) v.1 v.2
    ((@Law3734.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3735 takes them (153 nodes). -/
def ordS6A_Law3735 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3735. -/
theorem noS6A_Law3735 : ∀ v : Magma.tupS6A,
    ¬ @Equation3735 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3735) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3735) (by native_decide) v.1 v.2
    ((@Law3735.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3736 takes them (343 nodes). -/
def ordS6A_Law3736 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3736. -/
theorem noS6A_Law3736 : ∀ v : Magma.tupS6A,
    ¬ @Equation3736 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3736) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3736) (by native_decide) v.1 v.2
    ((@Law3736.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3738 takes them (69 nodes). -/
def ordS6A_Law3738 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3738. -/
theorem noS6A_Law3738 : ∀ v : Magma.tupS6A,
    ¬ @Equation3738 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3738) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3738) (by native_decide) v.1 v.2
    ((@Law3738.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3739 takes them (90 nodes). -/
def ordS6A_Law3739 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3739. -/
theorem noS6A_Law3739 : ∀ v : Magma.tupS6A,
    ¬ @Equation3739 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3739) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3739) (by native_decide) v.1 v.2
    ((@Law3739.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3740 takes them (165 nodes). -/
def ordS6A_Law3740 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3740. -/
theorem noS6A_Law3740 : ∀ v : Magma.tupS6A,
    ¬ @Equation3740 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3740) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3740) (by native_decide) v.1 v.2
    ((@Law3740.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3741 takes them (108 nodes). -/
def ordS6A_Law3741 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3741. -/
theorem noS6A_Law3741 : ∀ v : Magma.tupS6A,
    ¬ @Equation3741 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3741) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law3741) (by native_decide) v.1 v.2
    ((@Law3741.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3742 takes them (81 nodes). -/
def ordS6A_Law3742 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3742. -/
theorem noS6A_Law3742 : ∀ v : Magma.tupS6A,
    ¬ @Equation3742 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3742) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3742) (by native_decide) v.1 v.2
    ((@Law3742.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3743 takes them (50 nodes). -/
def ordS6A_Law3743 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3743. -/
theorem noS6A_Law3743 : ∀ v : Magma.tupS6A,
    ¬ @Equation3743 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3743) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3743) (by native_decide) v.1 v.2
    ((@Law3743.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3744 takes them (85 nodes). -/
def ordS6A_Law3744 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3744. -/
theorem noS6A_Law3744 : ∀ v : Magma.tupS6A,
    ¬ @Equation3744 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3744) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3744) (by native_decide) v.1 v.2
    ((@Law3744.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3745 takes them (50 nodes). -/
def ordS6A_Law3745 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3745. -/
theorem noS6A_Law3745 : ∀ v : Magma.tupS6A,
    ¬ @Equation3745 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3745) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3745) (by native_decide) v.1 v.2
    ((@Law3745.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3746 takes them (50 nodes). -/
def ordS6A_Law3746 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3746. -/
theorem noS6A_Law3746 : ∀ v : Magma.tupS6A,
    ¬ @Equation3746 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3746) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law3746) (by native_decide) v.1 v.2
    ((@Law3746.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `25` equations. -/
theorem srch6A_refutes_38 :
    FamilyRefutes Magma.srch6A [
      3654, 3655, 3656, 3657, 3658, 3711, 3713, 3717, 3718, 3719, 3720, 3731, 3733, 3734, 3735,
      3736, 3738, 3739, 3740, 3741, 3742, 3743, 3744, 3745, 3746
    ] :=
  ⟨noS6A_Law3654, noS6A_Law3655, noS6A_Law3656, noS6A_Law3657, noS6A_Law3658, noS6A_Law3711, noS6A_Law3713, noS6A_Law3717, noS6A_Law3718, noS6A_Law3719, noS6A_Law3720, noS6A_Law3731, noS6A_Law3733, noS6A_Law3734, noS6A_Law3735, noS6A_Law3736, noS6A_Law3738, noS6A_Law3739, noS6A_Law3740, noS6A_Law3741, noS6A_Law3742, noS6A_Law3743, noS6A_Law3744, noS6A_Law3745, noS6A_Law3746⟩
