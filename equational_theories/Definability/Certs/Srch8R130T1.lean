import equational_theories.Definability.Srch_S8R130

/-!
# Structural certificate targets: `Magma.srch8R130` (part 2 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R130_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 302 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R130_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 621 takes them (3 nodes). -/
def ordS8R130_Law621 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 621. -/
theorem noS8R130_Law621 : ∀ v : Magma.tup8R130,
    ¬ @Equation621 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law621) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law621) (by native_decide) v.1 v.2
    ((@Law621.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 622 takes them (4 nodes). -/
def ordS8R130_Law622 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 622. -/
theorem noS8R130_Law622 : ∀ v : Magma.tup8R130,
    ¬ @Equation622 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law622) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law622) (by native_decide) v.1 v.2
    ((@Law622.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 623 takes them (3 nodes). -/
def ordS8R130_Law623 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 623. -/
theorem noS8R130_Law623 : ∀ v : Magma.tup8R130,
    ¬ @Equation623 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law623) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law623) (by native_decide) v.1 v.2
    ((@Law623.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 624 takes them (3 nodes). -/
def ordS8R130_Law624 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 624. -/
theorem noS8R130_Law624 : ∀ v : Magma.tup8R130,
    ¬ @Equation624 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law624) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law624) (by native_decide) v.1 v.2
    ((@Law624.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 625 takes them (4 nodes). -/
def ordS8R130_Law625 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 625. -/
theorem noS8R130_Law625 : ∀ v : Magma.tup8R130,
    ¬ @Equation625 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law625) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law625) (by native_decide) v.1 v.2
    ((@Law625.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 626 takes them (3 nodes). -/
def ordS8R130_Law626 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 626. -/
theorem noS8R130_Law626 : ∀ v : Magma.tup8R130,
    ¬ @Equation626 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law626) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law626) (by native_decide) v.1 v.2
    ((@Law626.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 627 takes them (3 nodes). -/
def ordS8R130_Law627 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 627. -/
theorem noS8R130_Law627 : ∀ v : Magma.tup8R130,
    ¬ @Equation627 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law627) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law627) (by native_decide) v.1 v.2
    ((@Law627.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 628 takes them (3 nodes). -/
def ordS8R130_Law628 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 628. -/
theorem noS8R130_Law628 : ∀ v : Magma.tup8R130,
    ¬ @Equation628 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law628) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 4)
    (ord := ordS8R130_Law628) (by native_decide) v.1 v.2
    ((@Law628.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 630 takes them (3 nodes). -/
def ordS8R130_Law630 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 630. -/
theorem noS8R130_Law630 : ∀ v : Magma.tup8R130,
    ¬ @Equation630 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law630) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law630) (by native_decide) v.1 v.2
    ((@Law630.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 632 takes them (4 nodes). -/
def ordS8R130_Law632 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 632. -/
theorem noS8R130_Law632 : ∀ v : Magma.tup8R130,
    ¬ @Equation632 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law632) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law632) (by native_decide) v.1 v.2
    ((@Law632.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 639 takes them (4 nodes). -/
def ordS8R130_Law639 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 639. -/
theorem noS8R130_Law639 : ∀ v : Magma.tup8R130,
    ¬ @Equation639 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law639) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law639) (by native_decide) v.1 v.2
    ((@Law639.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 642 takes them (4 nodes). -/
def ordS8R130_Law642 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 642. -/
theorem noS8R130_Law642 : ∀ v : Magma.tup8R130,
    ¬ @Equation642 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law642) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law642) (by native_decide) v.1 v.2
    ((@Law642.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 643 takes them (3 nodes). -/
def ordS8R130_Law643 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 643. -/
theorem noS8R130_Law643 : ∀ v : Magma.tup8R130,
    ¬ @Equation643 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law643) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law643) (by native_decide) v.1 v.2
    ((@Law643.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 647 takes them (3 nodes). -/
def ordS8R130_Law647 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 647. -/
theorem noS8R130_Law647 : ∀ v : Magma.tup8R130,
    ¬ @Equation647 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law647) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law647) (by native_decide) v.1 v.2
    ((@Law647.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 655 takes them (3 nodes). -/
def ordS8R130_Law655 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 655. -/
theorem noS8R130_Law655 : ∀ v : Magma.tup8R130,
    ¬ @Equation655 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law655) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law655) (by native_decide) v.1 v.2
    ((@Law655.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 658 takes them (3 nodes). -/
def ordS8R130_Law658 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 658. -/
theorem noS8R130_Law658 : ∀ v : Magma.tup8R130,
    ¬ @Equation658 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law658) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law658) (by native_decide) v.1 v.2
    ((@Law658.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 669 takes them (3 nodes). -/
def ordS8R130_Law669 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 669. -/
theorem noS8R130_Law669 : ∀ v : Magma.tup8R130,
    ¬ @Equation669 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law669) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law669) (by native_decide) v.1 v.2
    ((@Law669.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 703 takes them (3 nodes). -/
def ordS8R130_Law703 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 703. -/
theorem noS8R130_Law703 : ∀ v : Magma.tup8R130,
    ¬ @Equation703 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law703) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law703) (by native_decide) v.1 v.2
    ((@Law703.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 716 takes them (3 nodes). -/
def ordS8R130_Law716 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 716. -/
theorem noS8R130_Law716 : ∀ v : Magma.tup8R130,
    ¬ @Equation716 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law716) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law716) (by native_decide) v.1 v.2
    ((@Law716.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 731 takes them (3 nodes). -/
def ordS8R130_Law731 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 731. -/
theorem noS8R130_Law731 : ∀ v : Magma.tup8R130,
    ¬ @Equation731 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law731) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law731) (by native_decide) v.1 v.2
    ((@Law731.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 765 takes them (3 nodes). -/
def ordS8R130_Law765 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 765. -/
theorem noS8R130_Law765 : ∀ v : Magma.tup8R130,
    ¬ @Equation765 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law765) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law765) (by native_decide) v.1 v.2
    ((@Law765.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 778 takes them (3 nodes). -/
def ordS8R130_Law778 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 778. -/
theorem noS8R130_Law778 : ∀ v : Magma.tup8R130,
    ¬ @Equation778 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law778) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law778) (by native_decide) v.1 v.2
    ((@Law778.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 818 takes them (3 nodes). -/
def ordS8R130_Law818 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 818. -/
theorem noS8R130_Law818 : ∀ v : Magma.tup8R130,
    ¬ @Equation818 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law818) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law818) (by native_decide) v.1 v.2
    ((@Law818.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 819 takes them (4 nodes). -/
def ordS8R130_Law819 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 819. -/
theorem noS8R130_Law819 : ∀ v : Magma.tup8R130,
    ¬ @Equation819 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law819) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law819) (by native_decide) v.1 v.2
    ((@Law819.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 820 takes them (3 nodes). -/
def ordS8R130_Law820 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 820. -/
theorem noS8R130_Law820 : ∀ v : Magma.tup8R130,
    ¬ @Equation820 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law820) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law820) (by native_decide) v.1 v.2
    ((@Law820.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 821 takes them (3 nodes). -/
def ordS8R130_Law821 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 821. -/
theorem noS8R130_Law821 : ∀ v : Magma.tup8R130,
    ¬ @Equation821 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law821) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law821) (by native_decide) v.1 v.2
    ((@Law821.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 822 takes them (4 nodes). -/
def ordS8R130_Law822 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 822. -/
theorem noS8R130_Law822 : ∀ v : Magma.tup8R130,
    ¬ @Equation822 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law822) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law822) (by native_decide) v.1 v.2
    ((@Law822.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 823 takes them (3 nodes). -/
def ordS8R130_Law823 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 823. -/
theorem noS8R130_Law823 : ∀ v : Magma.tup8R130,
    ¬ @Equation823 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law823) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law823) (by native_decide) v.1 v.2
    ((@Law823.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 826 takes them (3 nodes). -/
def ordS8R130_Law826 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 826. -/
theorem noS8R130_Law826 : ∀ v : Magma.tup8R130,
    ¬ @Equation826 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law826) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law826) (by native_decide) v.1 v.2
    ((@Law826.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 832 takes them (4 nodes). -/
def ordS8R130_Law832 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 832. -/
theorem noS8R130_Law832 : ∀ v : Magma.tup8R130,
    ¬ @Equation832 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law832) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law832) (by native_decide) v.1 v.2
    ((@Law832.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 833 takes them (3 nodes). -/
def ordS8R130_Law833 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 833. -/
theorem noS8R130_Law833 : ∀ v : Magma.tup8R130,
    ¬ @Equation833 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law833) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law833) (by native_decide) v.1 v.2
    ((@Law833.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 835 takes them (4 nodes). -/
def ordS8R130_Law835 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 835. -/
theorem noS8R130_Law835 : ∀ v : Magma.tup8R130,
    ¬ @Equation835 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law835) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law835) (by native_decide) v.1 v.2
    ((@Law835.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 836 takes them (3 nodes). -/
def ordS8R130_Law836 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 836. -/
theorem noS8R130_Law836 : ∀ v : Magma.tup8R130,
    ¬ @Equation836 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law836) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law836) (by native_decide) v.1 v.2
    ((@Law836.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 842 takes them (4 nodes). -/
def ordS8R130_Law842 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 842. -/
theorem noS8R130_Law842 : ∀ v : Magma.tup8R130,
    ¬ @Equation842 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law842) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law842) (by native_decide) v.1 v.2
    ((@Law842.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 843 takes them (3 nodes). -/
def ordS8R130_Law843 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 843. -/
theorem noS8R130_Law843 : ∀ v : Magma.tup8R130,
    ¬ @Equation843 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law843) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law843) (by native_decide) v.1 v.2
    ((@Law843.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 844 takes them (3 nodes). -/
def ordS8R130_Law844 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 844. -/
theorem noS8R130_Law844 : ∀ v : Magma.tup8R130,
    ¬ @Equation844 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law844) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law844) (by native_decide) v.1 v.2
    ((@Law844.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 845 takes them (4 nodes). -/
def ordS8R130_Law845 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 845. -/
theorem noS8R130_Law845 : ∀ v : Magma.tup8R130,
    ¬ @Equation845 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law845) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law845) (by native_decide) v.1 v.2
    ((@Law845.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 846 takes them (3 nodes). -/
def ordS8R130_Law846 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 846. -/
theorem noS8R130_Law846 : ∀ v : Magma.tup8R130,
    ¬ @Equation846 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law846) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law846) (by native_decide) v.1 v.2
    ((@Law846.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 847 takes them (3 nodes). -/
def ordS8R130_Law847 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 847. -/
theorem noS8R130_Law847 : ∀ v : Magma.tup8R130,
    ¬ @Equation847 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law847) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law847) (by native_decide) v.1 v.2
    ((@Law847.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 848 takes them (4 nodes). -/
def ordS8R130_Law848 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 848. -/
theorem noS8R130_Law848 : ∀ v : Magma.tup8R130,
    ¬ @Equation848 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law848) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law848) (by native_decide) v.1 v.2
    ((@Law848.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 849 takes them (3 nodes). -/
def ordS8R130_Law849 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 849. -/
theorem noS8R130_Law849 : ∀ v : Magma.tup8R130,
    ¬ @Equation849 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law849) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law849) (by native_decide) v.1 v.2
    ((@Law849.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 850 takes them (3 nodes). -/
def ordS8R130_Law850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 850. -/
theorem noS8R130_Law850 : ∀ v : Magma.tup8R130,
    ¬ @Equation850 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law850) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law850) (by native_decide) v.1 v.2
    ((@Law850.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 851 takes them (3 nodes). -/
def ordS8R130_Law851 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 851. -/
theorem noS8R130_Law851 : ∀ v : Magma.tup8R130,
    ¬ @Equation851 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law851) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 4)
    (ord := ordS8R130_Law851) (by native_decide) v.1 v.2
    ((@Law851.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 858 takes them (3 nodes). -/
def ordS8R130_Law858 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 858. -/
theorem noS8R130_Law858 : ∀ v : Magma.tup8R130,
    ¬ @Equation858 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law858) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law858) (by native_decide) v.1 v.2
    ((@Law858.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 861 takes them (3 nodes). -/
def ordS8R130_Law861 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 861. -/
theorem noS8R130_Law861 : ∀ v : Magma.tup8R130,
    ¬ @Equation861 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law861) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law861) (by native_decide) v.1 v.2
    ((@Law861.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 872 takes them (3 nodes). -/
def ordS8R130_Law872 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 872. -/
theorem noS8R130_Law872 : ∀ v : Magma.tup8R130,
    ¬ @Equation872 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law872) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law872) (by native_decide) v.1 v.2
    ((@Law872.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 879 takes them (3 nodes). -/
def ordS8R130_Law879 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 879. -/
theorem noS8R130_Law879 : ∀ v : Magma.tup8R130,
    ¬ @Equation879 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law879) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law879) (by native_decide) v.1 v.2
    ((@Law879.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 882 takes them (3 nodes). -/
def ordS8R130_Law882 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 882. -/
theorem noS8R130_Law882 : ∀ v : Magma.tup8R130,
    ¬ @Equation882 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law882) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law882) (by native_decide) v.1 v.2
    ((@Law882.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 906 takes them (3 nodes). -/
def ordS8R130_Law906 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 906. -/
theorem noS8R130_Law906 : ∀ v : Magma.tup8R130,
    ¬ @Equation906 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law906) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law906) (by native_decide) v.1 v.2
    ((@Law906.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 909 takes them (3 nodes). -/
def ordS8R130_Law909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 909. -/
theorem noS8R130_Law909 : ∀ v : Magma.tup8R130,
    ¬ @Equation909 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law909) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law909) (by native_decide) v.1 v.2
    ((@Law909.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 916 takes them (3 nodes). -/
def ordS8R130_Law916 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 916. -/
theorem noS8R130_Law916 : ∀ v : Magma.tup8R130,
    ¬ @Equation916 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law916) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law916) (by native_decide) v.1 v.2
    ((@Law916.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 919 takes them (3 nodes). -/
def ordS8R130_Law919 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 919. -/
theorem noS8R130_Law919 : ∀ v : Magma.tup8R130,
    ¬ @Equation919 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law919) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law919) (by native_decide) v.1 v.2
    ((@Law919.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 934 takes them (3 nodes). -/
def ordS8R130_Law934 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 934. -/
theorem noS8R130_Law934 : ∀ v : Magma.tup8R130,
    ¬ @Equation934 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law934) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law934) (by native_decide) v.1 v.2
    ((@Law934.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 968 takes them (3 nodes). -/
def ordS8R130_Law968 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 968. -/
theorem noS8R130_Law968 : ∀ v : Magma.tup8R130,
    ¬ @Equation968 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law968) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law968) (by native_decide) v.1 v.2
    ((@Law968.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 981 takes them (3 nodes). -/
def ordS8R130_Law981 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 981. -/
theorem noS8R130_Law981 : ∀ v : Magma.tup8R130,
    ¬ @Equation981 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law981) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law981) (by native_decide) v.1 v.2
    ((@Law981.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1021 takes them (3 nodes). -/
def ordS8R130_Law1021 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1021. -/
theorem noS8R130_Law1021 : ∀ v : Magma.tup8R130,
    ¬ @Equation1021 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1021) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1021) (by native_decide) v.1 v.2
    ((@Law1021.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1022 takes them (4 nodes). -/
def ordS8R130_Law1022 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1022. -/
theorem noS8R130_Law1022 : ∀ v : Magma.tup8R130,
    ¬ @Equation1022 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1022) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1022) (by native_decide) v.1 v.2
    ((@Law1022.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1023 takes them (3 nodes). -/
def ordS8R130_Law1023 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1023. -/
theorem noS8R130_Law1023 : ∀ v : Magma.tup8R130,
    ¬ @Equation1023 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1023) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1023) (by native_decide) v.1 v.2
    ((@Law1023.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1024 takes them (3 nodes). -/
def ordS8R130_Law1024 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1024. -/
theorem noS8R130_Law1024 : ∀ v : Magma.tup8R130,
    ¬ @Equation1024 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1024) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1024) (by native_decide) v.1 v.2
    ((@Law1024.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1025 takes them (4 nodes). -/
def ordS8R130_Law1025 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1025. -/
theorem noS8R130_Law1025 : ∀ v : Magma.tup8R130,
    ¬ @Equation1025 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1025) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1025) (by native_decide) v.1 v.2
    ((@Law1025.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1026 takes them (3 nodes). -/
def ordS8R130_Law1026 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1026. -/
theorem noS8R130_Law1026 : ∀ v : Magma.tup8R130,
    ¬ @Equation1026 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1026) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1026) (by native_decide) v.1 v.2
    ((@Law1026.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1028 takes them (4 nodes). -/
def ordS8R130_Law1028 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1028. -/
theorem noS8R130_Law1028 : ∀ v : Magma.tup8R130,
    ¬ @Equation1028 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1028) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1028) (by native_decide) v.1 v.2
    ((@Law1028.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1029 takes them (3 nodes). -/
def ordS8R130_Law1029 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1029. -/
theorem noS8R130_Law1029 : ∀ v : Magma.tup8R130,
    ¬ @Equation1029 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1029) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1029) (by native_decide) v.1 v.2
    ((@Law1029.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1031 takes them (4 nodes). -/
def ordS8R130_Law1031 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1031. -/
theorem noS8R130_Law1031 : ∀ v : Magma.tup8R130,
    ¬ @Equation1031 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1031) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1031) (by native_decide) v.1 v.2
    ((@Law1031.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1035 takes them (4 nodes). -/
def ordS8R130_Law1035 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1035. -/
theorem noS8R130_Law1035 : ∀ v : Magma.tup8R130,
    ¬ @Equation1035 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1035) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1035) (by native_decide) v.1 v.2
    ((@Law1035.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1036 takes them (3 nodes). -/
def ordS8R130_Law1036 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1036. -/
theorem noS8R130_Law1036 : ∀ v : Magma.tup8R130,
    ¬ @Equation1036 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1036) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1036) (by native_decide) v.1 v.2
    ((@Law1036.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1038 takes them (4 nodes). -/
def ordS8R130_Law1038 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1038. -/
theorem noS8R130_Law1038 : ∀ v : Magma.tup8R130,
    ¬ @Equation1038 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1038) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1038) (by native_decide) v.1 v.2
    ((@Law1038.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1045 takes them (4 nodes). -/
def ordS8R130_Law1045 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1045. -/
theorem noS8R130_Law1045 : ∀ v : Magma.tup8R130,
    ¬ @Equation1045 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1045) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1045) (by native_decide) v.1 v.2
    ((@Law1045.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1049 takes them (3 nodes). -/
def ordS8R130_Law1049 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1049. -/
theorem noS8R130_Law1049 : ∀ v : Magma.tup8R130,
    ¬ @Equation1049 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1049) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1049) (by native_decide) v.1 v.2
    ((@Law1049.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1053 takes them (3 nodes). -/
def ordS8R130_Law1053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1053. -/
theorem noS8R130_Law1053 : ∀ v : Magma.tup8R130,
    ¬ @Equation1053 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1053) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1053) (by native_decide) v.1 v.2
    ((@Law1053.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1061 takes them (3 nodes). -/
def ordS8R130_Law1061 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1061. -/
theorem noS8R130_Law1061 : ∀ v : Magma.tup8R130,
    ¬ @Equation1061 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1061) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1061) (by native_decide) v.1 v.2
    ((@Law1061.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1064 takes them (3 nodes). -/
def ordS8R130_Law1064 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1064. -/
theorem noS8R130_Law1064 : ∀ v : Magma.tup8R130,
    ¬ @Equation1064 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1064) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1064) (by native_decide) v.1 v.2
    ((@Law1064.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1075 takes them (3 nodes). -/
def ordS8R130_Law1075 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1075. -/
theorem noS8R130_Law1075 : ∀ v : Magma.tup8R130,
    ¬ @Equation1075 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1075) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1075) (by native_decide) v.1 v.2
    ((@Law1075.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1109 takes them (3 nodes). -/
def ordS8R130_Law1109 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1109. -/
theorem noS8R130_Law1109 : ∀ v : Magma.tup8R130,
    ¬ @Equation1109 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1109) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1109) (by native_decide) v.1 v.2
    ((@Law1109.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1122 takes them (3 nodes). -/
def ordS8R130_Law1122 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1122. -/
theorem noS8R130_Law1122 : ∀ v : Magma.tup8R130,
    ¬ @Equation1122 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1122) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1122) (by native_decide) v.1 v.2
    ((@Law1122.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1137 takes them (3 nodes). -/
def ordS8R130_Law1137 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1137. -/
theorem noS8R130_Law1137 : ∀ v : Magma.tup8R130,
    ¬ @Equation1137 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1137) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1137) (by native_decide) v.1 v.2
    ((@Law1137.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1171 takes them (3 nodes). -/
def ordS8R130_Law1171 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1171. -/
theorem noS8R130_Law1171 : ∀ v : Magma.tup8R130,
    ¬ @Equation1171 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1171) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1171) (by native_decide) v.1 v.2
    ((@Law1171.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1184 takes them (3 nodes). -/
def ordS8R130_Law1184 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1184. -/
theorem noS8R130_Law1184 : ∀ v : Magma.tup8R130,
    ¬ @Equation1184 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1184) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1184) (by native_decide) v.1 v.2
    ((@Law1184.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1224 takes them (3 nodes). -/
def ordS8R130_Law1224 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1224. -/
theorem noS8R130_Law1224 : ∀ v : Magma.tup8R130,
    ¬ @Equation1224 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1224) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1224) (by native_decide) v.1 v.2
    ((@Law1224.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1225 takes them (4 nodes). -/
def ordS8R130_Law1225 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1225. -/
theorem noS8R130_Law1225 : ∀ v : Magma.tup8R130,
    ¬ @Equation1225 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1225) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1225) (by native_decide) v.1 v.2
    ((@Law1225.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1226 takes them (3 nodes). -/
def ordS8R130_Law1226 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1226. -/
theorem noS8R130_Law1226 : ∀ v : Magma.tup8R130,
    ¬ @Equation1226 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1226) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1226) (by native_decide) v.1 v.2
    ((@Law1226.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1227 takes them (3 nodes). -/
def ordS8R130_Law1227 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1227. -/
theorem noS8R130_Law1227 : ∀ v : Magma.tup8R130,
    ¬ @Equation1227 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1227) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1227) (by native_decide) v.1 v.2
    ((@Law1227.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1228 takes them (4 nodes). -/
def ordS8R130_Law1228 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1228. -/
theorem noS8R130_Law1228 : ∀ v : Magma.tup8R130,
    ¬ @Equation1228 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1228) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1228) (by native_decide) v.1 v.2
    ((@Law1228.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1229 takes them (3 nodes). -/
def ordS8R130_Law1229 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1229. -/
theorem noS8R130_Law1229 : ∀ v : Magma.tup8R130,
    ¬ @Equation1229 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1229) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1229) (by native_decide) v.1 v.2
    ((@Law1229.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1231 takes them (4 nodes). -/
def ordS8R130_Law1231 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1231. -/
theorem noS8R130_Law1231 : ∀ v : Magma.tup8R130,
    ¬ @Equation1231 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1231) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1231) (by native_decide) v.1 v.2
    ((@Law1231.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1232 takes them (3 nodes). -/
def ordS8R130_Law1232 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1232. -/
theorem noS8R130_Law1232 : ∀ v : Magma.tup8R130,
    ¬ @Equation1232 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1232) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1232) (by native_decide) v.1 v.2
    ((@Law1232.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1238 takes them (4 nodes). -/
def ordS8R130_Law1238 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1238. -/
theorem noS8R130_Law1238 : ∀ v : Magma.tup8R130,
    ¬ @Equation1238 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1238) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1238) (by native_decide) v.1 v.2
    ((@Law1238.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1241 takes them (4 nodes). -/
def ordS8R130_Law1241 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1241. -/
theorem noS8R130_Law1241 : ∀ v : Magma.tup8R130,
    ¬ @Equation1241 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1241) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1241) (by native_decide) v.1 v.2
    ((@Law1241.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1248 takes them (4 nodes). -/
def ordS8R130_Law1248 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1248. -/
theorem noS8R130_Law1248 : ∀ v : Magma.tup8R130,
    ¬ @Equation1248 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1248) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1248) (by native_decide) v.1 v.2
    ((@Law1248.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1249 takes them (3 nodes). -/
def ordS8R130_Law1249 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1249. -/
theorem noS8R130_Law1249 : ∀ v : Magma.tup8R130,
    ¬ @Equation1249 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1249) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1249) (by native_decide) v.1 v.2
    ((@Law1249.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1250 takes them (3 nodes). -/
def ordS8R130_Law1250 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1250. -/
theorem noS8R130_Law1250 : ∀ v : Magma.tup8R130,
    ¬ @Equation1250 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1250) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 3)
    (ord := ordS8R130_Law1250) (by native_decide) v.1 v.2
    ((@Law1250.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1251 takes them (4 nodes). -/
def ordS8R130_Law1251 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 1251. -/
theorem noS8R130_Law1251 : ∀ v : Magma.tup8R130,
    ¬ @Equation1251 (Fin 8) (Magma.srch8R130 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1251) (E := S8R130.E) (tr := S8R130.tr) (z := S8R130.z)
    (st := S8R130.st) (X := S8R130.X) (envs := Magma.envsRed 8 S8R130.E 2)
    (ord := ordS8R130_Law1251) (by native_decide) v.1 v.2
    ((@Law1251.models_iff (Fin 8) (Magma.srch8R130 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch8R130_refutes_1 :
    FamilyRefutes Magma.srch8R130 [
      621, 622, 623, 624, 625, 626, 627, 628, 630, 632, 639, 642, 643, 647, 655, 658, 669, 703,
      716, 731, 765, 778, 818, 819, 820, 821, 822, 823, 826, 832, 833, 835, 836, 842, 843, 844,
      845, 846, 847, 848, 849, 850, 851, 858, 861, 872, 879, 882, 906, 909, 916, 919, 934, 968,
      981, 1021, 1022, 1023, 1024, 1025, 1026, 1028, 1029, 1031, 1035, 1036, 1038, 1045, 1049,
      1053, 1061, 1064, 1075, 1109, 1122, 1137, 1171, 1184, 1224, 1225, 1226, 1227, 1228, 1229,
      1231, 1232, 1238, 1241, 1248, 1249, 1250, 1251
    ] :=
  ⟨noS8R130_Law621, noS8R130_Law622, noS8R130_Law623, noS8R130_Law624, noS8R130_Law625, noS8R130_Law626, noS8R130_Law627, noS8R130_Law628, noS8R130_Law630, noS8R130_Law632, noS8R130_Law639, noS8R130_Law642, noS8R130_Law643, noS8R130_Law647, noS8R130_Law655, noS8R130_Law658, noS8R130_Law669, noS8R130_Law703, noS8R130_Law716, noS8R130_Law731, noS8R130_Law765, noS8R130_Law778, noS8R130_Law818, noS8R130_Law819, noS8R130_Law820, noS8R130_Law821, noS8R130_Law822, noS8R130_Law823, noS8R130_Law826, noS8R130_Law832, noS8R130_Law833, noS8R130_Law835, noS8R130_Law836, noS8R130_Law842, noS8R130_Law843, noS8R130_Law844, noS8R130_Law845, noS8R130_Law846, noS8R130_Law847, noS8R130_Law848, noS8R130_Law849, noS8R130_Law850, noS8R130_Law851, noS8R130_Law858, noS8R130_Law861, noS8R130_Law872, noS8R130_Law879, noS8R130_Law882, noS8R130_Law906, noS8R130_Law909, noS8R130_Law916, noS8R130_Law919, noS8R130_Law934, noS8R130_Law968, noS8R130_Law981, noS8R130_Law1021, noS8R130_Law1022, noS8R130_Law1023, noS8R130_Law1024, noS8R130_Law1025, noS8R130_Law1026, noS8R130_Law1028, noS8R130_Law1029, noS8R130_Law1031, noS8R130_Law1035, noS8R130_Law1036, noS8R130_Law1038, noS8R130_Law1045, noS8R130_Law1049, noS8R130_Law1053, noS8R130_Law1061, noS8R130_Law1064, noS8R130_Law1075, noS8R130_Law1109, noS8R130_Law1122, noS8R130_Law1137, noS8R130_Law1171, noS8R130_Law1184, noS8R130_Law1224, noS8R130_Law1225, noS8R130_Law1226, noS8R130_Law1227, noS8R130_Law1228, noS8R130_Law1229, noS8R130_Law1231, noS8R130_Law1232, noS8R130_Law1238, noS8R130_Law1241, noS8R130_Law1248, noS8R130_Law1249, noS8R130_Law1250, noS8R130_Law1251⟩
