import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 7 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `24`
equations here, 2,969 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 662 takes them (69 nodes). -/
def ordS6A_Law662 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 662. -/
theorem noS6A_Law662 : ∀ v : Magma.tupS6A,
    ¬ @Equation662 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law662) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law662) (by native_decide) v.1 v.2
    ((@Law662.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 663 takes them (66 nodes). -/
def ordS6A_Law663 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 663. -/
theorem noS6A_Law663 : ∀ v : Magma.tupS6A,
    ¬ @Equation663 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law663) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law663) (by native_decide) v.1 v.2
    ((@Law663.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 664 takes them (76 nodes). -/
def ordS6A_Law664 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 664. -/
theorem noS6A_Law664 : ∀ v : Magma.tupS6A,
    ¬ @Equation664 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law664) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law664) (by native_decide) v.1 v.2
    ((@Law664.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 665 takes them (38 nodes). -/
def ordS6A_Law665 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 665. -/
theorem noS6A_Law665 : ∀ v : Magma.tupS6A,
    ¬ @Equation665 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law665) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law665) (by native_decide) v.1 v.2
    ((@Law665.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 666 takes them (203 nodes). -/
def ordS6A_Law666 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 666. -/
theorem noS6A_Law666 : ∀ v : Magma.tupS6A,
    ¬ @Equation666 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law666) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law666) (by native_decide) v.1 v.2
    ((@Law666.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 672 takes them (79 nodes). -/
def ordS6A_Law672 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 672. -/
theorem noS6A_Law672 : ∀ v : Magma.tupS6A,
    ¬ @Equation672 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law672) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law672) (by native_decide) v.1 v.2
    ((@Law672.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 676 takes them (583 nodes). -/
def ordS6A_Law676 : List (Fin 11) := [8, 9, 6, 10, 5, 2, 7, 1, 4, 3, 0]

/-- No member of the class satisfies equation 676. -/
theorem noS6A_Law676 : ∀ v : Magma.tupS6A,
    ¬ @Equation676 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law676) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law676) (by native_decide) v.1 v.2
    ((@Law676.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 679 takes them (300 nodes). -/
def ordS6A_Law679 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 679. -/
theorem noS6A_Law679 : ∀ v : Magma.tupS6A,
    ¬ @Equation679 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law679) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law679) (by native_decide) v.1 v.2
    ((@Law679.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 682 takes them (84 nodes). -/
def ordS6A_Law682 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 682. -/
theorem noS6A_Law682 : ∀ v : Magma.tupS6A,
    ¬ @Equation682 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law682) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law682) (by native_decide) v.1 v.2
    ((@Law682.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 686 takes them (117 nodes). -/
def ordS6A_Law686 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 686. -/
theorem noS6A_Law686 : ∀ v : Magma.tupS6A,
    ¬ @Equation686 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law686) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law686) (by native_decide) v.1 v.2
    ((@Law686.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 690 takes them (129 nodes). -/
def ordS6A_Law690 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 690. -/
theorem noS6A_Law690 : ∀ v : Magma.tupS6A,
    ¬ @Equation690 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law690) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law690) (by native_decide) v.1 v.2
    ((@Law690.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 694 takes them (152 nodes). -/
def ordS6A_Law694 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 694. -/
theorem noS6A_Law694 : ∀ v : Magma.tupS6A,
    ¬ @Equation694 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law694) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law694) (by native_decide) v.1 v.2
    ((@Law694.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 698 takes them (78 nodes). -/
def ordS6A_Law698 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 698. -/
theorem noS6A_Law698 : ∀ v : Magma.tupS6A,
    ¬ @Equation698 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law698) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law698) (by native_decide) v.1 v.2
    ((@Law698.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 709 takes them (121 nodes). -/
def ordS6A_Law709 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 709. -/
theorem noS6A_Law709 : ∀ v : Magma.tupS6A,
    ¬ @Equation709 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law709) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law709) (by native_decide) v.1 v.2
    ((@Law709.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 713 takes them (142 nodes). -/
def ordS6A_Law713 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 713. -/
theorem noS6A_Law713 : ∀ v : Magma.tupS6A,
    ¬ @Equation713 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law713) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law713) (by native_decide) v.1 v.2
    ((@Law713.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 719 takes them (28 nodes). -/
def ordS6A_Law719 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 719. -/
theorem noS6A_Law719 : ∀ v : Magma.tupS6A,
    ¬ @Equation719 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law719) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law719) (by native_decide) v.1 v.2
    ((@Law719.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 723 takes them (54 nodes). -/
def ordS6A_Law723 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 723. -/
theorem noS6A_Law723 : ∀ v : Magma.tupS6A,
    ¬ @Equation723 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law723) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law723) (by native_decide) v.1 v.2
    ((@Law723.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 735 takes them (28 nodes). -/
def ordS6A_Law735 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 735. -/
theorem noS6A_Law735 : ∀ v : Magma.tupS6A,
    ¬ @Equation735 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law735) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law735) (by native_decide) v.1 v.2
    ((@Law735.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 740 takes them (197 nodes). -/
def ordS6A_Law740 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 740. -/
theorem noS6A_Law740 : ∀ v : Magma.tupS6A,
    ¬ @Equation740 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law740) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law740) (by native_decide) v.1 v.2
    ((@Law740.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 744 takes them (116 nodes). -/
def ordS6A_Law744 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 744. -/
theorem noS6A_Law744 : ∀ v : Magma.tupS6A,
    ¬ @Equation744 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law744) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law744) (by native_decide) v.1 v.2
    ((@Law744.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 748 takes them (97 nodes). -/
def ordS6A_Law748 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 748. -/
theorem noS6A_Law748 : ∀ v : Magma.tupS6A,
    ¬ @Equation748 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law748) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law748) (by native_decide) v.1 v.2
    ((@Law748.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 752 takes them (66 nodes). -/
def ordS6A_Law752 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 752. -/
theorem noS6A_Law752 : ∀ v : Magma.tupS6A,
    ¬ @Equation752 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law752) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law752) (by native_decide) v.1 v.2
    ((@Law752.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 757 takes them (45 nodes). -/
def ordS6A_Law757 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 757. -/
theorem noS6A_Law757 : ∀ v : Magma.tupS6A,
    ¬ @Equation757 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law757) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law757) (by native_decide) v.1 v.2
    ((@Law757.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 761 takes them (101 nodes). -/
def ordS6A_Law761 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 761. -/
theorem noS6A_Law761 : ∀ v : Magma.tupS6A,
    ¬ @Equation761 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law761) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law761) (by native_decide) v.1 v.2
    ((@Law761.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `24` equations. -/
theorem srch6A_refutes_6 :
    FamilyRefutes Magma.srch6A [
      662, 663, 664, 665, 666, 672, 676, 679, 682, 686, 690, 694, 698, 709, 713, 719, 723, 735,
      740, 744, 748, 752, 757, 761
    ] :=
  ⟨noS6A_Law662, noS6A_Law663, noS6A_Law664, noS6A_Law665, noS6A_Law666, noS6A_Law672, noS6A_Law676, noS6A_Law679, noS6A_Law682, noS6A_Law686, noS6A_Law690, noS6A_Law694, noS6A_Law698, noS6A_Law709, noS6A_Law713, noS6A_Law719, noS6A_Law723, noS6A_Law735, noS6A_Law740, noS6A_Law744, noS6A_Law748, noS6A_Law752, noS6A_Law757, noS6A_Law761⟩
