import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 151 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `41`
equations here, 2,048 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2667 takes them (184 nodes). -/
def ordS8R9_Law2667 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2667. -/
theorem noS8R9_Law2667 : ∀ v : Magma.tup8R9,
    ¬ @Equation2667 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2667) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2667) (by native_decide) v.1 v.2
    ((@Law2667.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2668 takes them (9 nodes). -/
def ordS8R9_Law2668 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2668. -/
theorem noS8R9_Law2668 : ∀ v : Magma.tup8R9,
    ¬ @Equation2668 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2668) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2668) (by native_decide) v.1 v.2
    ((@Law2668.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2670 takes them (540 nodes). -/
def ordS8R9_Law2670 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2670. -/
theorem noS8R9_Law2670 : ∀ v : Magma.tup8R9,
    ¬ @Equation2670 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2670) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law2670) (by native_decide) v.1 v.2
    ((@Law2670.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2671 takes them (9 nodes). -/
def ordS8R9_Law2671 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2671. -/
theorem noS8R9_Law2671 : ∀ v : Magma.tup8R9,
    ¬ @Equation2671 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2671) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2671) (by native_decide) v.1 v.2
    ((@Law2671.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2674 takes them (9 nodes). -/
def ordS8R9_Law2674 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2674. -/
theorem noS8R9_Law2674 : ∀ v : Magma.tup8R9,
    ¬ @Equation2674 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2674) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2674) (by native_decide) v.1 v.2
    ((@Law2674.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2676 takes them (70 nodes). -/
def ordS8R9_Law2676 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2676. -/
theorem noS8R9_Law2676 : ∀ v : Magma.tup8R9,
    ¬ @Equation2676 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2676) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2676) (by native_decide) v.1 v.2
    ((@Law2676.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2677 takes them (81 nodes). -/
def ordS8R9_Law2677 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2677. -/
theorem noS8R9_Law2677 : ∀ v : Magma.tup8R9,
    ¬ @Equation2677 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2677) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2677) (by native_decide) v.1 v.2
    ((@Law2677.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2678 takes them (9 nodes). -/
def ordS8R9_Law2678 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2678. -/
theorem noS8R9_Law2678 : ∀ v : Magma.tup8R9,
    ¬ @Equation2678 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2678) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2678) (by native_decide) v.1 v.2
    ((@Law2678.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2680 takes them (57 nodes). -/
def ordS8R9_Law2680 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2680. -/
theorem noS8R9_Law2680 : ∀ v : Magma.tup8R9,
    ¬ @Equation2680 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2680) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2680) (by native_decide) v.1 v.2
    ((@Law2680.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2681 takes them (47 nodes). -/
def ordS8R9_Law2681 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2681. -/
theorem noS8R9_Law2681 : ∀ v : Magma.tup8R9,
    ¬ @Equation2681 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2681) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2681) (by native_decide) v.1 v.2
    ((@Law2681.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2682 takes them (9 nodes). -/
def ordS8R9_Law2682 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2682. -/
theorem noS8R9_Law2682 : ∀ v : Magma.tup8R9,
    ¬ @Equation2682 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2682) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2682) (by native_decide) v.1 v.2
    ((@Law2682.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2684 takes them (172 nodes). -/
def ordS8R9_Law2684 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2684. -/
theorem noS8R9_Law2684 : ∀ v : Magma.tup8R9,
    ¬ @Equation2684 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2684) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2684) (by native_decide) v.1 v.2
    ((@Law2684.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2685 takes them (143 nodes). -/
def ordS8R9_Law2685 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2685. -/
theorem noS8R9_Law2685 : ∀ v : Magma.tup8R9,
    ¬ @Equation2685 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2685) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2685) (by native_decide) v.1 v.2
    ((@Law2685.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2686 takes them (9 nodes). -/
def ordS8R9_Law2686 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2686. -/
theorem noS8R9_Law2686 : ∀ v : Magma.tup8R9,
    ¬ @Equation2686 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2686) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2686) (by native_decide) v.1 v.2
    ((@Law2686.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2688 takes them (19 nodes). -/
def ordS8R9_Law2688 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2688. -/
theorem noS8R9_Law2688 : ∀ v : Magma.tup8R9,
    ¬ @Equation2688 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2688) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2688) (by native_decide) v.1 v.2
    ((@Law2688.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2689 takes them (73 nodes). -/
def ordS8R9_Law2689 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2689. -/
theorem noS8R9_Law2689 : ∀ v : Magma.tup8R9,
    ¬ @Equation2689 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2689) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2689) (by native_decide) v.1 v.2
    ((@Law2689.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2690 takes them (9 nodes). -/
def ordS8R9_Law2690 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2690. -/
theorem noS8R9_Law2690 : ∀ v : Magma.tup8R9,
    ¬ @Equation2690 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2690) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2690) (by native_decide) v.1 v.2
    ((@Law2690.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2692 takes them (19 nodes). -/
def ordS8R9_Law2692 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2692. -/
theorem noS8R9_Law2692 : ∀ v : Magma.tup8R9,
    ¬ @Equation2692 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2692) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2692) (by native_decide) v.1 v.2
    ((@Law2692.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2693 takes them (13 nodes). -/
def ordS8R9_Law2693 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2693. -/
theorem noS8R9_Law2693 : ∀ v : Magma.tup8R9,
    ¬ @Equation2693 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2693) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2693) (by native_decide) v.1 v.2
    ((@Law2693.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2694 takes them (15 nodes). -/
def ordS8R9_Law2694 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2694. -/
theorem noS8R9_Law2694 : ∀ v : Magma.tup8R9,
    ¬ @Equation2694 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2694) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2694) (by native_decide) v.1 v.2
    ((@Law2694.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2695 takes them (9 nodes). -/
def ordS8R9_Law2695 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2695. -/
theorem noS8R9_Law2695 : ∀ v : Magma.tup8R9,
    ¬ @Equation2695 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2695) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law2695) (by native_decide) v.1 v.2
    ((@Law2695.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2720 takes them (154 nodes). -/
def ordS8R9_Law2720 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2720. -/
theorem noS8R9_Law2720 : ∀ v : Magma.tup8R9,
    ¬ @Equation2720 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2720) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2720) (by native_decide) v.1 v.2
    ((@Law2720.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2724 takes them (64 nodes). -/
def ordS8R9_Law2724 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2724. -/
theorem noS8R9_Law2724 : ∀ v : Magma.tup8R9,
    ¬ @Equation2724 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2724) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2724) (by native_decide) v.1 v.2
    ((@Law2724.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2728 takes them (64 nodes). -/
def ordS8R9_Law2728 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2728. -/
theorem noS8R9_Law2728 : ∀ v : Magma.tup8R9,
    ¬ @Equation2728 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2728) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2728) (by native_decide) v.1 v.2
    ((@Law2728.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2739 takes them (62 nodes). -/
def ordS8R9_Law2739 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2739. -/
theorem noS8R9_Law2739 : ∀ v : Magma.tup8R9,
    ¬ @Equation2739 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2739) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2739) (by native_decide) v.1 v.2
    ((@Law2739.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2746 takes them (9 nodes). -/
def ordS8R9_Law2746 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2746. -/
theorem noS8R9_Law2746 : ∀ v : Magma.tup8R9,
    ¬ @Equation2746 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2746) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law2746) (by native_decide) v.1 v.2
    ((@Law2746.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2749 takes them (9 nodes). -/
def ordS8R9_Law2749 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2749. -/
theorem noS8R9_Law2749 : ∀ v : Magma.tup8R9,
    ¬ @Equation2749 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2749) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2749) (by native_decide) v.1 v.2
    ((@Law2749.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2757 takes them (9 nodes). -/
def ordS8R9_Law2757 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2757. -/
theorem noS8R9_Law2757 : ∀ v : Magma.tup8R9,
    ¬ @Equation2757 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2757) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2757) (by native_decide) v.1 v.2
    ((@Law2757.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2761 takes them (9 nodes). -/
def ordS8R9_Law2761 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2761. -/
theorem noS8R9_Law2761 : ∀ v : Magma.tup8R9,
    ¬ @Equation2761 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2761) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2761) (by native_decide) v.1 v.2
    ((@Law2761.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2765 takes them (9 nodes). -/
def ordS8R9_Law2765 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2765. -/
theorem noS8R9_Law2765 : ∀ v : Magma.tup8R9,
    ¬ @Equation2765 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2765) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2765) (by native_decide) v.1 v.2
    ((@Law2765.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2782 takes them (62 nodes). -/
def ordS8R9_Law2782 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2782. -/
theorem noS8R9_Law2782 : ∀ v : Magma.tup8R9,
    ¬ @Equation2782 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2782) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2782) (by native_decide) v.1 v.2
    ((@Law2782.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2791 takes them (9 nodes). -/
def ordS8R9_Law2791 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2791. -/
theorem noS8R9_Law2791 : ∀ v : Magma.tup8R9,
    ¬ @Equation2791 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2791) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2791) (by native_decide) v.1 v.2
    ((@Law2791.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2795 takes them (9 nodes). -/
def ordS8R9_Law2795 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2795. -/
theorem noS8R9_Law2795 : ∀ v : Magma.tup8R9,
    ¬ @Equation2795 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2795) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2795) (by native_decide) v.1 v.2
    ((@Law2795.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2799 takes them (9 nodes). -/
def ordS8R9_Law2799 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2799. -/
theorem noS8R9_Law2799 : ∀ v : Magma.tup8R9,
    ¬ @Equation2799 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2799) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2799) (by native_decide) v.1 v.2
    ((@Law2799.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2808 takes them (9 nodes). -/
def ordS8R9_Law2808 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2808. -/
theorem noS8R9_Law2808 : ∀ v : Magma.tup8R9,
    ¬ @Equation2808 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2808) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2808) (by native_decide) v.1 v.2
    ((@Law2808.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2812 takes them (9 nodes). -/
def ordS8R9_Law2812 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2812. -/
theorem noS8R9_Law2812 : ∀ v : Magma.tup8R9,
    ¬ @Equation2812 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2812) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2812) (by native_decide) v.1 v.2
    ((@Law2812.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2816 takes them (9 nodes). -/
def ordS8R9_Law2816 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2816. -/
theorem noS8R9_Law2816 : ∀ v : Magma.tup8R9,
    ¬ @Equation2816 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2816) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2816) (by native_decide) v.1 v.2
    ((@Law2816.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2826 takes them (9 nodes). -/
def ordS8R9_Law2826 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2826. -/
theorem noS8R9_Law2826 : ∀ v : Magma.tup8R9,
    ¬ @Equation2826 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2826) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2826) (by native_decide) v.1 v.2
    ((@Law2826.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2831 takes them (9 nodes). -/
def ordS8R9_Law2831 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2831. -/
theorem noS8R9_Law2831 : ∀ v : Magma.tup8R9,
    ¬ @Equation2831 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2831) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2831) (by native_decide) v.1 v.2
    ((@Law2831.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2836 takes them (9 nodes). -/
def ordS8R9_Law2836 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2836. -/
theorem noS8R9_Law2836 : ∀ v : Magma.tup8R9,
    ¬ @Equation2836 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2836) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2836) (by native_decide) v.1 v.2
    ((@Law2836.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2841 takes them (11 nodes). -/
def ordS8R9_Law2841 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2841. -/
theorem noS8R9_Law2841 : ∀ v : Magma.tup8R9,
    ¬ @Equation2841 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2841) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law2841) (by native_decide) v.1 v.2
    ((@Law2841.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `41` equations. -/
theorem srch8R9_refutes_150 :
    FamilyRefutes Magma.srch8R9 [
      2667, 2668, 2670, 2671, 2674, 2676, 2677, 2678, 2680, 2681, 2682, 2684, 2685, 2686, 2688,
      2689, 2690, 2692, 2693, 2694, 2695, 2720, 2724, 2728, 2739, 2746, 2749, 2757, 2761, 2765,
      2782, 2791, 2795, 2799, 2808, 2812, 2816, 2826, 2831, 2836, 2841
    ] :=
  ⟨noS8R9_Law2667, noS8R9_Law2668, noS8R9_Law2670, noS8R9_Law2671, noS8R9_Law2674, noS8R9_Law2676, noS8R9_Law2677, noS8R9_Law2678, noS8R9_Law2680, noS8R9_Law2681, noS8R9_Law2682, noS8R9_Law2684, noS8R9_Law2685, noS8R9_Law2686, noS8R9_Law2688, noS8R9_Law2689, noS8R9_Law2690, noS8R9_Law2692, noS8R9_Law2693, noS8R9_Law2694, noS8R9_Law2695, noS8R9_Law2720, noS8R9_Law2724, noS8R9_Law2728, noS8R9_Law2739, noS8R9_Law2746, noS8R9_Law2749, noS8R9_Law2757, noS8R9_Law2761, noS8R9_Law2765, noS8R9_Law2782, noS8R9_Law2791, noS8R9_Law2795, noS8R9_Law2799, noS8R9_Law2808, noS8R9_Law2812, noS8R9_Law2816, noS8R9_Law2826, noS8R9_Law2831, noS8R9_Law2836, noS8R9_Law2841⟩
