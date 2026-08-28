import equational_theories.Definability.Srch_S11R173

/-!
# Structural certificate targets: `Magma.srch11R173` (part 5 of 9)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S11R173_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `92` equations here, 301 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S11R173_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2706 takes them (3 nodes). -/
def ordS11R173_Law2706 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2706. -/
theorem noS11R173_Law2706 : ∀ v : Magma.tup11R173,
    ¬ @Equation2706 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2706) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2706) (by native_decide) v.1 v.2
    ((@Law2706.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2709 takes them (3 nodes). -/
def ordS11R173_Law2709 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2709. -/
theorem noS11R173_Law2709 : ∀ v : Magma.tup11R173,
    ¬ @Equation2709 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2709) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2709) (by native_decide) v.1 v.2
    ((@Law2709.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2712 takes them (3 nodes). -/
def ordS11R173_Law2712 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2712. -/
theorem noS11R173_Law2712 : ∀ v : Magma.tup11R173,
    ¬ @Equation2712 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2712) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2712) (by native_decide) v.1 v.2
    ((@Law2712.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2716 takes them (3 nodes). -/
def ordS11R173_Law2716 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2716. -/
theorem noS11R173_Law2716 : ∀ v : Magma.tup11R173,
    ¬ @Equation2716 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2716) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2716) (by native_decide) v.1 v.2
    ((@Law2716.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2733 takes them (3 nodes). -/
def ordS11R173_Law2733 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2733. -/
theorem noS11R173_Law2733 : ∀ v : Magma.tup11R173,
    ¬ @Equation2733 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2733) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2733) (by native_decide) v.1 v.2
    ((@Law2733.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2736 takes them (3 nodes). -/
def ordS11R173_Law2736 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2736. -/
theorem noS11R173_Law2736 : ∀ v : Magma.tup11R173,
    ¬ @Equation2736 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2736) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2736) (by native_decide) v.1 v.2
    ((@Law2736.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2753 takes them (3 nodes). -/
def ordS11R173_Law2753 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2753. -/
theorem noS11R173_Law2753 : ∀ v : Magma.tup11R173,
    ¬ @Equation2753 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2753) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2753) (by native_decide) v.1 v.2
    ((@Law2753.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2770 takes them (3 nodes). -/
def ordS11R173_Law2770 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2770. -/
theorem noS11R173_Law2770 : ∀ v : Magma.tup11R173,
    ¬ @Equation2770 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2770) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2770) (by native_decide) v.1 v.2
    ((@Law2770.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2774 takes them (3 nodes). -/
def ordS11R173_Law2774 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2774. -/
theorem noS11R173_Law2774 : ∀ v : Magma.tup11R173,
    ¬ @Equation2774 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2774) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2774) (by native_decide) v.1 v.2
    ((@Law2774.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2778 takes them (3 nodes). -/
def ordS11R173_Law2778 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2778. -/
theorem noS11R173_Law2778 : ∀ v : Magma.tup11R173,
    ¬ @Equation2778 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2778) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2778) (by native_decide) v.1 v.2
    ((@Law2778.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2787 takes them (3 nodes). -/
def ordS11R173_Law2787 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2787. -/
theorem noS11R173_Law2787 : ∀ v : Magma.tup11R173,
    ¬ @Equation2787 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2787) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2787) (by native_decide) v.1 v.2
    ((@Law2787.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2804 takes them (3 nodes). -/
def ordS11R173_Law2804 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2804. -/
theorem noS11R173_Law2804 : ∀ v : Magma.tup11R173,
    ¬ @Equation2804 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2804) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2804) (by native_decide) v.1 v.2
    ((@Law2804.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2821 takes them (3 nodes). -/
def ordS11R173_Law2821 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2821. -/
theorem noS11R173_Law2821 : ∀ v : Magma.tup11R173,
    ¬ @Equation2821 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2821) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law2821) (by native_decide) v.1 v.2
    ((@Law2821.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2849 takes them (4 nodes). -/
def ordS11R173_Law2849 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2849. -/
theorem noS11R173_Law2849 : ∀ v : Magma.tup11R173,
    ¬ @Equation2849 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2849) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2849) (by native_decide) v.1 v.2
    ((@Law2849.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2852 takes them (4 nodes). -/
def ordS11R173_Law2852 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2852. -/
theorem noS11R173_Law2852 : ∀ v : Magma.tup11R173,
    ¬ @Equation2852 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2852) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2852) (by native_decide) v.1 v.2
    ((@Law2852.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2858 takes them (4 nodes). -/
def ordS11R173_Law2858 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2858. -/
theorem noS11R173_Law2858 : ∀ v : Magma.tup11R173,
    ¬ @Equation2858 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2858) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2858) (by native_decide) v.1 v.2
    ((@Law2858.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2862 takes them (4 nodes). -/
def ordS11R173_Law2862 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2862. -/
theorem noS11R173_Law2862 : ∀ v : Magma.tup11R173,
    ¬ @Equation2862 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2862) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2862) (by native_decide) v.1 v.2
    ((@Law2862.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2865 takes them (4 nodes). -/
def ordS11R173_Law2865 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2865. -/
theorem noS11R173_Law2865 : ∀ v : Magma.tup11R173,
    ¬ @Equation2865 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2865) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2865) (by native_decide) v.1 v.2
    ((@Law2865.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2868 takes them (4 nodes). -/
def ordS11R173_Law2868 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2868. -/
theorem noS11R173_Law2868 : ∀ v : Magma.tup11R173,
    ¬ @Equation2868 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2868) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2868) (by native_decide) v.1 v.2
    ((@Law2868.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2872 takes them (4 nodes). -/
def ordS11R173_Law2872 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2872. -/
theorem noS11R173_Law2872 : ∀ v : Magma.tup11R173,
    ¬ @Equation2872 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2872) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2872) (by native_decide) v.1 v.2
    ((@Law2872.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2873 takes them (3 nodes). -/
def ordS11R173_Law2873 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2873. -/
theorem noS11R173_Law2873 : ∀ v : Magma.tup11R173,
    ¬ @Equation2873 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2873) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2873) (by native_decide) v.1 v.2
    ((@Law2873.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2876 takes them (3 nodes). -/
def ordS11R173_Law2876 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2876. -/
theorem noS11R173_Law2876 : ∀ v : Magma.tup11R173,
    ¬ @Equation2876 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2876) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2876) (by native_decide) v.1 v.2
    ((@Law2876.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2878 takes them (4 nodes). -/
def ordS11R173_Law2878 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2878. -/
theorem noS11R173_Law2878 : ∀ v : Magma.tup11R173,
    ¬ @Equation2878 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2878) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2878) (by native_decide) v.1 v.2
    ((@Law2878.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2882 takes them (4 nodes). -/
def ordS11R173_Law2882 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2882. -/
theorem noS11R173_Law2882 : ∀ v : Magma.tup11R173,
    ¬ @Equation2882 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2882) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2882) (by native_decide) v.1 v.2
    ((@Law2882.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2886 takes them (4 nodes). -/
def ordS11R173_Law2886 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2886. -/
theorem noS11R173_Law2886 : ∀ v : Magma.tup11R173,
    ¬ @Equation2886 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2886) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2886) (by native_decide) v.1 v.2
    ((@Law2886.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2890 takes them (4 nodes). -/
def ordS11R173_Law2890 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2890. -/
theorem noS11R173_Law2890 : ∀ v : Magma.tup11R173,
    ¬ @Equation2890 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2890) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2890) (by native_decide) v.1 v.2
    ((@Law2890.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2894 takes them (4 nodes). -/
def ordS11R173_Law2894 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2894. -/
theorem noS11R173_Law2894 : ∀ v : Magma.tup11R173,
    ¬ @Equation2894 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2894) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law2894) (by native_decide) v.1 v.2
    ((@Law2894.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2899 takes them (3 nodes). -/
def ordS11R173_Law2899 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2899. -/
theorem noS11R173_Law2899 : ∀ v : Magma.tup11R173,
    ¬ @Equation2899 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2899) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2899) (by native_decide) v.1 v.2
    ((@Law2899.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2909 takes them (3 nodes). -/
def ordS11R173_Law2909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2909. -/
theorem noS11R173_Law2909 : ∀ v : Magma.tup11R173,
    ¬ @Equation2909 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2919 takes them (3 nodes). -/
def ordS11R173_Law2919 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2919. -/
theorem noS11R173_Law2919 : ∀ v : Magma.tup11R173,
    ¬ @Equation2919 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2919) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2919) (by native_decide) v.1 v.2
    ((@Law2919.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2946 takes them (3 nodes). -/
def ordS11R173_Law2946 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2946. -/
theorem noS11R173_Law2946 : ∀ v : Magma.tup11R173,
    ¬ @Equation2946 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2946) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law2946) (by native_decide) v.1 v.2
    ((@Law2946.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2956 takes them (3 nodes). -/
def ordS11R173_Law2956 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2956. -/
theorem noS11R173_Law2956 : ∀ v : Magma.tup11R173,
    ¬ @Equation2956 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2956) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2956) (by native_decide) v.1 v.2
    ((@Law2956.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2973 takes them (3 nodes). -/
def ordS11R173_Law2973 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2973. -/
theorem noS11R173_Law2973 : ∀ v : Magma.tup11R173,
    ¬ @Equation2973 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2973) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2973) (by native_decide) v.1 v.2
    ((@Law2973.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2990 takes them (3 nodes). -/
def ordS11R173_Law2990 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2990. -/
theorem noS11R173_Law2990 : ∀ v : Magma.tup11R173,
    ¬ @Equation2990 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2990) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law2990) (by native_decide) v.1 v.2
    ((@Law2990.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3007 takes them (3 nodes). -/
def ordS11R173_Law3007 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3007. -/
theorem noS11R173_Law3007 : ∀ v : Magma.tup11R173,
    ¬ @Equation3007 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3007) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3007) (by native_decide) v.1 v.2
    ((@Law3007.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3024 takes them (3 nodes). -/
def ordS11R173_Law3024 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3024. -/
theorem noS11R173_Law3024 : ∀ v : Magma.tup11R173,
    ¬ @Equation3024 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3024) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3024) (by native_decide) v.1 v.2
    ((@Law3024.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3051 takes them (3 nodes). -/
def ordS11R173_Law3051 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3051. -/
theorem noS11R173_Law3051 : ∀ v : Magma.tup11R173,
    ¬ @Equation3051 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3051) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3051) (by native_decide) v.1 v.2
    ((@Law3051.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3052 takes them (4 nodes). -/
def ordS11R173_Law3052 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3052. -/
theorem noS11R173_Law3052 : ∀ v : Magma.tup11R173,
    ¬ @Equation3052 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3052) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3052) (by native_decide) v.1 v.2
    ((@Law3052.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3054 takes them (3 nodes). -/
def ordS11R173_Law3054 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3054. -/
theorem noS11R173_Law3054 : ∀ v : Magma.tup11R173,
    ¬ @Equation3054 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3054) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3054) (by native_decide) v.1 v.2
    ((@Law3054.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3055 takes them (4 nodes). -/
def ordS11R173_Law3055 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3055. -/
theorem noS11R173_Law3055 : ∀ v : Magma.tup11R173,
    ¬ @Equation3055 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3055) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3055) (by native_decide) v.1 v.2
    ((@Law3055.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3056 takes them (3 nodes). -/
def ordS11R173_Law3056 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3056. -/
theorem noS11R173_Law3056 : ∀ v : Magma.tup11R173,
    ¬ @Equation3056 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3056) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3056) (by native_decide) v.1 v.2
    ((@Law3056.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3057 takes them (3 nodes). -/
def ordS11R173_Law3057 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3057. -/
theorem noS11R173_Law3057 : ∀ v : Magma.tup11R173,
    ¬ @Equation3057 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3057) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3057) (by native_decide) v.1 v.2
    ((@Law3057.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3059 takes them (3 nodes). -/
def ordS11R173_Law3059 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3059. -/
theorem noS11R173_Law3059 : ∀ v : Magma.tup11R173,
    ¬ @Equation3059 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3059) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3059) (by native_decide) v.1 v.2
    ((@Law3059.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3060 takes them (3 nodes). -/
def ordS11R173_Law3060 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3060. -/
theorem noS11R173_Law3060 : ∀ v : Magma.tup11R173,
    ¬ @Equation3060 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3060) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3060) (by native_decide) v.1 v.2
    ((@Law3060.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3061 takes them (4 nodes). -/
def ordS11R173_Law3061 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3061. -/
theorem noS11R173_Law3061 : ∀ v : Magma.tup11R173,
    ¬ @Equation3061 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3061) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3061) (by native_decide) v.1 v.2
    ((@Law3061.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3062 takes them (3 nodes). -/
def ordS11R173_Law3062 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3062. -/
theorem noS11R173_Law3062 : ∀ v : Magma.tup11R173,
    ¬ @Equation3062 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3062) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3062) (by native_decide) v.1 v.2
    ((@Law3062.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3063 takes them (3 nodes). -/
def ordS11R173_Law3063 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3063. -/
theorem noS11R173_Law3063 : ∀ v : Magma.tup11R173,
    ¬ @Equation3063 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3063) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3063) (by native_decide) v.1 v.2
    ((@Law3063.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3064 takes them (3 nodes). -/
def ordS11R173_Law3064 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3064. -/
theorem noS11R173_Law3064 : ∀ v : Magma.tup11R173,
    ¬ @Equation3064 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3064) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3064) (by native_decide) v.1 v.2
    ((@Law3064.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3065 takes them (4 nodes). -/
def ordS11R173_Law3065 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3065. -/
theorem noS11R173_Law3065 : ∀ v : Magma.tup11R173,
    ¬ @Equation3065 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3065) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3065) (by native_decide) v.1 v.2
    ((@Law3065.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3067 takes them (3 nodes). -/
def ordS11R173_Law3067 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3067. -/
theorem noS11R173_Law3067 : ∀ v : Magma.tup11R173,
    ¬ @Equation3067 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3067) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3067) (by native_decide) v.1 v.2
    ((@Law3067.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3068 takes them (4 nodes). -/
def ordS11R173_Law3068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3068. -/
theorem noS11R173_Law3068 : ∀ v : Magma.tup11R173,
    ¬ @Equation3068 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3068) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3068) (by native_decide) v.1 v.2
    ((@Law3068.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3070 takes them (3 nodes). -/
def ordS11R173_Law3070 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3070. -/
theorem noS11R173_Law3070 : ∀ v : Magma.tup11R173,
    ¬ @Equation3070 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3070) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3070) (by native_decide) v.1 v.2
    ((@Law3070.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3071 takes them (4 nodes). -/
def ordS11R173_Law3071 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3071. -/
theorem noS11R173_Law3071 : ∀ v : Magma.tup11R173,
    ¬ @Equation3071 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3071) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3071) (by native_decide) v.1 v.2
    ((@Law3071.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3072 takes them (3 nodes). -/
def ordS11R173_Law3072 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3072. -/
theorem noS11R173_Law3072 : ∀ v : Magma.tup11R173,
    ¬ @Equation3072 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3072) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3072) (by native_decide) v.1 v.2
    ((@Law3072.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3073 takes them (3 nodes). -/
def ordS11R173_Law3073 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3073. -/
theorem noS11R173_Law3073 : ∀ v : Magma.tup11R173,
    ¬ @Equation3073 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3073) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3073) (by native_decide) v.1 v.2
    ((@Law3073.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3074 takes them (3 nodes). -/
def ordS11R173_Law3074 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3074. -/
theorem noS11R173_Law3074 : ∀ v : Magma.tup11R173,
    ¬ @Equation3074 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3074) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3074) (by native_decide) v.1 v.2
    ((@Law3074.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3077 takes them (3 nodes). -/
def ordS11R173_Law3077 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3077. -/
theorem noS11R173_Law3077 : ∀ v : Magma.tup11R173,
    ¬ @Equation3077 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3077) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3077) (by native_decide) v.1 v.2
    ((@Law3077.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3078 takes them (4 nodes). -/
def ordS11R173_Law3078 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3078. -/
theorem noS11R173_Law3078 : ∀ v : Magma.tup11R173,
    ¬ @Equation3078 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3078) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3078) (by native_decide) v.1 v.2
    ((@Law3078.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3080 takes them (3 nodes). -/
def ordS11R173_Law3080 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3080. -/
theorem noS11R173_Law3080 : ∀ v : Magma.tup11R173,
    ¬ @Equation3080 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3080) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3080) (by native_decide) v.1 v.2
    ((@Law3080.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3081 takes them (4 nodes). -/
def ordS11R173_Law3081 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3081. -/
theorem noS11R173_Law3081 : ∀ v : Magma.tup11R173,
    ¬ @Equation3081 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3081) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3081) (by native_decide) v.1 v.2
    ((@Law3081.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3082 takes them (3 nodes). -/
def ordS11R173_Law3082 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3082. -/
theorem noS11R173_Law3082 : ∀ v : Magma.tup11R173,
    ¬ @Equation3082 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3082) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3082) (by native_decide) v.1 v.2
    ((@Law3082.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3084 takes them (3 nodes). -/
def ordS11R173_Law3084 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3084. -/
theorem noS11R173_Law3084 : ∀ v : Magma.tup11R173,
    ¬ @Equation3084 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3084) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3084) (by native_decide) v.1 v.2
    ((@Law3084.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3085 takes them (4 nodes). -/
def ordS11R173_Law3085 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3085. -/
theorem noS11R173_Law3085 : ∀ v : Magma.tup11R173,
    ¬ @Equation3085 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3085) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3085) (by native_decide) v.1 v.2
    ((@Law3085.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3086 takes them (3 nodes). -/
def ordS11R173_Law3086 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3086. -/
theorem noS11R173_Law3086 : ∀ v : Magma.tup11R173,
    ¬ @Equation3086 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3086) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3086) (by native_decide) v.1 v.2
    ((@Law3086.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3087 takes them (3 nodes). -/
def ordS11R173_Law3087 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3087. -/
theorem noS11R173_Law3087 : ∀ v : Magma.tup11R173,
    ¬ @Equation3087 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3087) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3087) (by native_decide) v.1 v.2
    ((@Law3087.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3088 takes them (3 nodes). -/
def ordS11R173_Law3088 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3088. -/
theorem noS11R173_Law3088 : ∀ v : Magma.tup11R173,
    ¬ @Equation3088 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3088) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3088) (by native_decide) v.1 v.2
    ((@Law3088.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3089 takes them (4 nodes). -/
def ordS11R173_Law3089 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3089. -/
theorem noS11R173_Law3089 : ∀ v : Magma.tup11R173,
    ¬ @Equation3089 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3089) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3089) (by native_decide) v.1 v.2
    ((@Law3089.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3090 takes them (3 nodes). -/
def ordS11R173_Law3090 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3090. -/
theorem noS11R173_Law3090 : ∀ v : Magma.tup11R173,
    ¬ @Equation3090 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3090) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3090) (by native_decide) v.1 v.2
    ((@Law3090.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (3 nodes). -/
def ordS11R173_Law3091 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3091. -/
theorem noS11R173_Law3091 : ∀ v : Magma.tup11R173,
    ¬ @Equation3091 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3092 takes them (3 nodes). -/
def ordS11R173_Law3092 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3092. -/
theorem noS11R173_Law3092 : ∀ v : Magma.tup11R173,
    ¬ @Equation3092 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3092) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3092) (by native_decide) v.1 v.2
    ((@Law3092.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3093 takes them (4 nodes). -/
def ordS11R173_Law3093 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3093. -/
theorem noS11R173_Law3093 : ∀ v : Magma.tup11R173,
    ¬ @Equation3093 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3093) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3093) (by native_decide) v.1 v.2
    ((@Law3093.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3095 takes them (3 nodes). -/
def ordS11R173_Law3095 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3095. -/
theorem noS11R173_Law3095 : ∀ v : Magma.tup11R173,
    ¬ @Equation3095 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3095) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3095) (by native_decide) v.1 v.2
    ((@Law3095.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3096 takes them (3 nodes). -/
def ordS11R173_Law3096 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3096. -/
theorem noS11R173_Law3096 : ∀ v : Magma.tup11R173,
    ¬ @Equation3096 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3096) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3096) (by native_decide) v.1 v.2
    ((@Law3096.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3097 takes them (4 nodes). -/
def ordS11R173_Law3097 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3097. -/
theorem noS11R173_Law3097 : ∀ v : Magma.tup11R173,
    ¬ @Equation3097 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3097) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3097) (by native_decide) v.1 v.2
    ((@Law3097.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3098 takes them (3 nodes). -/
def ordS11R173_Law3098 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3098. -/
theorem noS11R173_Law3098 : ∀ v : Magma.tup11R173,
    ¬ @Equation3098 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3098) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3098) (by native_decide) v.1 v.2
    ((@Law3098.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3099 takes them (3 nodes). -/
def ordS11R173_Law3099 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3099. -/
theorem noS11R173_Law3099 : ∀ v : Magma.tup11R173,
    ¬ @Equation3099 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3099) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3099) (by native_decide) v.1 v.2
    ((@Law3099.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3100 takes them (3 nodes). -/
def ordS11R173_Law3100 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3100. -/
theorem noS11R173_Law3100 : ∀ v : Magma.tup11R173,
    ¬ @Equation3100 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3100) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3100) (by native_decide) v.1 v.2
    ((@Law3100.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3102 takes them (3 nodes). -/
def ordS11R173_Law3102 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3102. -/
theorem noS11R173_Law3102 : ∀ v : Magma.tup11R173,
    ¬ @Equation3102 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3102) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3102) (by native_decide) v.1 v.2
    ((@Law3102.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3108 takes them (3 nodes). -/
def ordS11R173_Law3108 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3108. -/
theorem noS11R173_Law3108 : ∀ v : Magma.tup11R173,
    ¬ @Equation3108 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3108) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3108) (by native_decide) v.1 v.2
    ((@Law3108.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (3 nodes). -/
def ordS11R173_Law3112 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3112. -/
theorem noS11R173_Law3112 : ∀ v : Magma.tup11R173,
    ¬ @Equation3112 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3122 takes them (3 nodes). -/
def ordS11R173_Law3122 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3122. -/
theorem noS11R173_Law3122 : ∀ v : Magma.tup11R173,
    ¬ @Equation3122 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3122) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3122) (by native_decide) v.1 v.2
    ((@Law3122.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3139 takes them (3 nodes). -/
def ordS11R173_Law3139 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3139. -/
theorem noS11R173_Law3139 : ∀ v : Magma.tup11R173,
    ¬ @Equation3139 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3139) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3139) (by native_decide) v.1 v.2
    ((@Law3139.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (3 nodes). -/
def ordS11R173_Law3142 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3142. -/
theorem noS11R173_Law3142 : ∀ v : Magma.tup11R173,
    ¬ @Equation3142 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3149 takes them (3 nodes). -/
def ordS11R173_Law3149 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3149. -/
theorem noS11R173_Law3149 : ∀ v : Magma.tup11R173,
    ¬ @Equation3149 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3149) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3149) (by native_decide) v.1 v.2
    ((@Law3149.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3159 takes them (3 nodes). -/
def ordS11R173_Law3159 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3159. -/
theorem noS11R173_Law3159 : ∀ v : Magma.tup11R173,
    ¬ @Equation3159 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3159) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3159) (by native_decide) v.1 v.2
    ((@Law3159.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3176 takes them (3 nodes). -/
def ordS11R173_Law3176 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3176. -/
theorem noS11R173_Law3176 : ∀ v : Magma.tup11R173,
    ¬ @Equation3176 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3176) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3176) (by native_decide) v.1 v.2
    ((@Law3176.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3180 takes them (3 nodes). -/
def ordS11R173_Law3180 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3180. -/
theorem noS11R173_Law3180 : ∀ v : Magma.tup11R173,
    ¬ @Equation3180 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3180) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3180) (by native_decide) v.1 v.2
    ((@Law3180.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3193 takes them (3 nodes). -/
def ordS11R173_Law3193 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3193. -/
theorem noS11R173_Law3193 : ∀ v : Magma.tup11R173,
    ¬ @Equation3193 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3193) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3193) (by native_decide) v.1 v.2
    ((@Law3193.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3210 takes them (3 nodes). -/
def ordS11R173_Law3210 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3210. -/
theorem noS11R173_Law3210 : ∀ v : Magma.tup11R173,
    ¬ @Equation3210 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3210) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 3)
    (ord := ordS11R173_Law3210) (by native_decide) v.1 v.2
    ((@Law3210.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3227 takes them (3 nodes). -/
def ordS11R173_Law3227 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3227. -/
theorem noS11R173_Law3227 : ∀ v : Magma.tup11R173,
    ¬ @Equation3227 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3227) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 4)
    (ord := ordS11R173_Law3227) (by native_decide) v.1 v.2
    ((@Law3227.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3254 takes them (3 nodes). -/
def ordS11R173_Law3254 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3254. -/
theorem noS11R173_Law3254 : ∀ v : Magma.tup11R173,
    ¬ @Equation3254 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3254) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3254) (by native_decide) v.1 v.2
    ((@Law3254.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3255 takes them (4 nodes). -/
def ordS11R173_Law3255 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3255. -/
theorem noS11R173_Law3255 : ∀ v : Magma.tup11R173,
    ¬ @Equation3255 (Fin 11) (Magma.srch11R173 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3255) (E := S11R173.E) (tr := S11R173.tr) (z := S11R173.z)
    (st := S11R173.st) (X := S11R173.X) (envs := Magma.envsRed 11 S11R173.E 2)
    (ord := ordS11R173_Law3255) (by native_decide) v.1 v.2
    ((@Law3255.models_iff (Fin 11) (Magma.srch11R173 v)).mpr hv)

/-- No member of the class satisfies any of these `92` equations. -/
theorem srch11R173_refutes_4 :
    FamilyRefutes Magma.srch11R173 [
      2706, 2709, 2712, 2716, 2733, 2736, 2753, 2770, 2774, 2778, 2787, 2804, 2821, 2849, 2852,
      2858, 2862, 2865, 2868, 2872, 2873, 2876, 2878, 2882, 2886, 2890, 2894, 2899, 2909, 2919,
      2946, 2956, 2973, 2990, 3007, 3024, 3051, 3052, 3054, 3055, 3056, 3057, 3059, 3060, 3061,
      3062, 3063, 3064, 3065, 3067, 3068, 3070, 3071, 3072, 3073, 3074, 3077, 3078, 3080, 3081,
      3082, 3084, 3085, 3086, 3087, 3088, 3089, 3090, 3091, 3092, 3093, 3095, 3096, 3097, 3098,
      3099, 3100, 3102, 3108, 3112, 3122, 3139, 3142, 3149, 3159, 3176, 3180, 3193, 3210, 3227,
      3254, 3255
    ] :=
  ⟨noS11R173_Law2706, noS11R173_Law2709, noS11R173_Law2712, noS11R173_Law2716, noS11R173_Law2733, noS11R173_Law2736, noS11R173_Law2753, noS11R173_Law2770, noS11R173_Law2774, noS11R173_Law2778, noS11R173_Law2787, noS11R173_Law2804, noS11R173_Law2821, noS11R173_Law2849, noS11R173_Law2852, noS11R173_Law2858, noS11R173_Law2862, noS11R173_Law2865, noS11R173_Law2868, noS11R173_Law2872, noS11R173_Law2873, noS11R173_Law2876, noS11R173_Law2878, noS11R173_Law2882, noS11R173_Law2886, noS11R173_Law2890, noS11R173_Law2894, noS11R173_Law2899, noS11R173_Law2909, noS11R173_Law2919, noS11R173_Law2946, noS11R173_Law2956, noS11R173_Law2973, noS11R173_Law2990, noS11R173_Law3007, noS11R173_Law3024, noS11R173_Law3051, noS11R173_Law3052, noS11R173_Law3054, noS11R173_Law3055, noS11R173_Law3056, noS11R173_Law3057, noS11R173_Law3059, noS11R173_Law3060, noS11R173_Law3061, noS11R173_Law3062, noS11R173_Law3063, noS11R173_Law3064, noS11R173_Law3065, noS11R173_Law3067, noS11R173_Law3068, noS11R173_Law3070, noS11R173_Law3071, noS11R173_Law3072, noS11R173_Law3073, noS11R173_Law3074, noS11R173_Law3077, noS11R173_Law3078, noS11R173_Law3080, noS11R173_Law3081, noS11R173_Law3082, noS11R173_Law3084, noS11R173_Law3085, noS11R173_Law3086, noS11R173_Law3087, noS11R173_Law3088, noS11R173_Law3089, noS11R173_Law3090, noS11R173_Law3091, noS11R173_Law3092, noS11R173_Law3093, noS11R173_Law3095, noS11R173_Law3096, noS11R173_Law3097, noS11R173_Law3098, noS11R173_Law3099, noS11R173_Law3100, noS11R173_Law3102, noS11R173_Law3108, noS11R173_Law3112, noS11R173_Law3122, noS11R173_Law3139, noS11R173_Law3142, noS11R173_Law3149, noS11R173_Law3159, noS11R173_Law3176, noS11R173_Law3180, noS11R173_Law3193, noS11R173_Law3210, noS11R173_Law3227, noS11R173_Law3254, noS11R173_Law3255⟩
