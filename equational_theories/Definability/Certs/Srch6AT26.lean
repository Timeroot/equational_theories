import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 27 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `25`
equations here, 2,935 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2690 takes them (65 nodes). -/
def ordS6A_Law2690 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2690. -/
theorem noS6A_Law2690 : ∀ v : Magma.tupS6A,
    ¬ @Equation2690 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2690) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2690) (by native_decide) v.1 v.2
    ((@Law2690.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2692 takes them (149 nodes). -/
def ordS6A_Law2692 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2692. -/
theorem noS6A_Law2692 : ∀ v : Magma.tupS6A,
    ¬ @Equation2692 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2692) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2692) (by native_decide) v.1 v.2
    ((@Law2692.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2693 takes them (103 nodes). -/
def ordS6A_Law2693 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2693. -/
theorem noS6A_Law2693 : ∀ v : Magma.tupS6A,
    ¬ @Equation2693 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2693) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2693) (by native_decide) v.1 v.2
    ((@Law2693.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2694 takes them (73 nodes). -/
def ordS6A_Law2694 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2694. -/
theorem noS6A_Law2694 : ∀ v : Magma.tupS6A,
    ¬ @Equation2694 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2694) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2694) (by native_decide) v.1 v.2
    ((@Law2694.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2695 takes them (38 nodes). -/
def ordS6A_Law2695 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2695. -/
theorem noS6A_Law2695 : ∀ v : Magma.tupS6A,
    ¬ @Equation2695 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2695) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2695) (by native_decide) v.1 v.2
    ((@Law2695.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2720 takes them (84 nodes). -/
def ordS6A_Law2720 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2720. -/
theorem noS6A_Law2720 : ∀ v : Magma.tupS6A,
    ¬ @Equation2720 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2720) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2720) (by native_decide) v.1 v.2
    ((@Law2720.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2728 takes them (78 nodes). -/
def ordS6A_Law2728 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2728. -/
theorem noS6A_Law2728 : ∀ v : Magma.tupS6A,
    ¬ @Equation2728 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2728) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2728) (by native_decide) v.1 v.2
    ((@Law2728.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2749 takes them (117 nodes). -/
def ordS6A_Law2749 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2749. -/
theorem noS6A_Law2749 : ∀ v : Magma.tupS6A,
    ¬ @Equation2749 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2749) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2749) (by native_decide) v.1 v.2
    ((@Law2749.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2757 takes them (141 nodes). -/
def ordS6A_Law2757 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2757. -/
theorem noS6A_Law2757 : ∀ v : Magma.tupS6A,
    ¬ @Equation2757 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2757) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2757) (by native_decide) v.1 v.2
    ((@Law2757.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2765 takes them (108 nodes). -/
def ordS6A_Law2765 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2765. -/
theorem noS6A_Law2765 : ∀ v : Magma.tupS6A,
    ¬ @Equation2765 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2765) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2765) (by native_decide) v.1 v.2
    ((@Law2765.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2799 takes them (52 nodes). -/
def ordS6A_Law2799 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2799. -/
theorem noS6A_Law2799 : ∀ v : Magma.tupS6A,
    ¬ @Equation2799 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2799) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2799) (by native_decide) v.1 v.2
    ((@Law2799.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2816 takes them (66 nodes). -/
def ordS6A_Law2816 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2816. -/
theorem noS6A_Law2816 : ∀ v : Magma.tupS6A,
    ¬ @Equation2816 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2816) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2816) (by native_decide) v.1 v.2
    ((@Law2816.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2826 takes them (38 nodes). -/
def ordS6A_Law2826 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2826. -/
theorem noS6A_Law2826 : ∀ v : Magma.tupS6A,
    ¬ @Equation2826 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2826) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2826) (by native_decide) v.1 v.2
    ((@Law2826.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2831 takes them (76 nodes). -/
def ordS6A_Law2831 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2831. -/
theorem noS6A_Law2831 : ∀ v : Magma.tupS6A,
    ¬ @Equation2831 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2831) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2831) (by native_decide) v.1 v.2
    ((@Law2831.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2841 takes them (38 nodes). -/
def ordS6A_Law2841 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2841. -/
theorem noS6A_Law2841 : ∀ v : Magma.tupS6A,
    ¬ @Equation2841 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2841) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law2841) (by native_decide) v.1 v.2
    ((@Law2841.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2848 takes them (146 nodes). -/
def ordS6A_Law2848 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2848. -/
theorem noS6A_Law2848 : ∀ v : Magma.tupS6A,
    ¬ @Equation2848 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2848) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2848) (by native_decide) v.1 v.2
    ((@Law2848.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2851 takes them (97 nodes). -/
def ordS6A_Law2851 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2851. -/
theorem noS6A_Law2851 : ∀ v : Magma.tupS6A,
    ¬ @Equation2851 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2851) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2851) (by native_decide) v.1 v.2
    ((@Law2851.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2853 takes them (621 nodes). -/
def ordS6A_Law2853 : List (Fin 11) := [10, 5, 1, 2, 9, 8, 4, 6, 7, 3, 0]

/-- No member of the class satisfies equation 2853. -/
theorem noS6A_Law2853 : ∀ v : Magma.tupS6A,
    ¬ @Equation2853 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2853) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2853) (by native_decide) v.1 v.2
    ((@Law2853.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2854 takes them (85 nodes). -/
def ordS6A_Law2854 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2854. -/
theorem noS6A_Law2854 : ∀ v : Magma.tupS6A,
    ¬ @Equation2854 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2854) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2854) (by native_decide) v.1 v.2
    ((@Law2854.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2856 takes them (281 nodes). -/
def ordS6A_Law2856 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2856. -/
theorem noS6A_Law2856 : ∀ v : Magma.tupS6A,
    ¬ @Equation2856 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2856) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 2)
    (ord := ordS6A_Law2856) (by native_decide) v.1 v.2
    ((@Law2856.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2857 takes them (94 nodes). -/
def ordS6A_Law2857 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2857. -/
theorem noS6A_Law2857 : ∀ v : Magma.tupS6A,
    ¬ @Equation2857 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2857) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2857) (by native_decide) v.1 v.2
    ((@Law2857.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2859 takes them (100 nodes). -/
def ordS6A_Law2859 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2859. -/
theorem noS6A_Law2859 : ∀ v : Magma.tupS6A,
    ¬ @Equation2859 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2859) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2859) (by native_decide) v.1 v.2
    ((@Law2859.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2860 takes them (154 nodes). -/
def ordS6A_Law2860 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2860. -/
theorem noS6A_Law2860 : ∀ v : Magma.tupS6A,
    ¬ @Equation2860 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2860) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2860) (by native_decide) v.1 v.2
    ((@Law2860.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2861 takes them (40 nodes). -/
def ordS6A_Law2861 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2861. -/
theorem noS6A_Law2861 : ∀ v : Magma.tupS6A,
    ¬ @Equation2861 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2861) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2861) (by native_decide) v.1 v.2
    ((@Law2861.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2864 takes them (91 nodes). -/
def ordS6A_Law2864 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2864. -/
theorem noS6A_Law2864 : ∀ v : Magma.tupS6A,
    ¬ @Equation2864 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2864) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2864) (by native_decide) v.1 v.2
    ((@Law2864.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `25` equations. -/
theorem srch6A_refutes_26 :
    FamilyRefutes Magma.srch6A [
      2690, 2692, 2693, 2694, 2695, 2720, 2728, 2749, 2757, 2765, 2799, 2816, 2826, 2831, 2841,
      2848, 2851, 2853, 2854, 2856, 2857, 2859, 2860, 2861, 2864
    ] :=
  ⟨noS6A_Law2690, noS6A_Law2692, noS6A_Law2693, noS6A_Law2694, noS6A_Law2695, noS6A_Law2720, noS6A_Law2728, noS6A_Law2749, noS6A_Law2757, noS6A_Law2765, noS6A_Law2799, noS6A_Law2816, noS6A_Law2826, noS6A_Law2831, noS6A_Law2841, noS6A_Law2848, noS6A_Law2851, noS6A_Law2853, noS6A_Law2854, noS6A_Law2856, noS6A_Law2857, noS6A_Law2859, noS6A_Law2860, noS6A_Law2861, noS6A_Law2864⟩
