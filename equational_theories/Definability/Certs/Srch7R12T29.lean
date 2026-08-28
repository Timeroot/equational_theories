import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 30 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `11` equations here, 3,313 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2850 takes them (596 nodes). -/
def ordS7R12_Law2850 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2850. -/
theorem noS7R12_Law2850 : ∀ v : Magma.tup7R12,
    ¬ @Equation2850 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2858 takes them (165 nodes). -/
def ordS7R12_Law2858 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2858. -/
theorem noS7R12_Law2858 : ∀ v : Magma.tup7R12,
    ¬ @Equation2858 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2858) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2858) (by native_decide) v.1 v.2
    ((@Law2858.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2868 takes them (187 nodes). -/
def ordS7R12_Law2868 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2868. -/
theorem noS7R12_Law2868 : ∀ v : Magma.tup7R12,
    ¬ @Equation2868 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2868) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2868) (by native_decide) v.1 v.2
    ((@Law2868.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2875 takes them (617 nodes). -/
def ordS7R12_Law2875 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2875. -/
theorem noS7R12_Law2875 : ∀ v : Magma.tup7R12,
    ¬ @Equation2875 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2875) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2875) (by native_decide) v.1 v.2
    ((@Law2875.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2876 takes them (333 nodes). -/
def ordS7R12_Law2876 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2876. -/
theorem noS7R12_Law2876 : ∀ v : Magma.tup7R12,
    ¬ @Equation2876 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2876) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law2876) (by native_decide) v.1 v.2
    ((@Law2876.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2878 takes them (286 nodes). -/
def ordS7R12_Law2878 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2878. -/
theorem noS7R12_Law2878 : ∀ v : Magma.tup7R12,
    ¬ @Equation2878 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2878) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2878) (by native_decide) v.1 v.2
    ((@Law2878.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2880 takes them (272 nodes). -/
def ordS7R12_Law2880 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2880. -/
theorem noS7R12_Law2880 : ∀ v : Magma.tup7R12,
    ¬ @Equation2880 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2880) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2880) (by native_decide) v.1 v.2
    ((@Law2880.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2886 takes them (185 nodes). -/
def ordS7R12_Law2886 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2886. -/
theorem noS7R12_Law2886 : ∀ v : Magma.tup7R12,
    ¬ @Equation2886 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2886) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2886) (by native_decide) v.1 v.2
    ((@Law2886.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2890 takes them (208 nodes). -/
def ordS7R12_Law2890 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2890. -/
theorem noS7R12_Law2890 : ∀ v : Magma.tup7R12,
    ¬ @Equation2890 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2890) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2890) (by native_decide) v.1 v.2
    ((@Law2890.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2894 takes them (120 nodes). -/
def ordS7R12_Law2894 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2894. -/
theorem noS7R12_Law2894 : ∀ v : Magma.tup7R12,
    ¬ @Equation2894 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2894) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2894) (by native_decide) v.1 v.2
    ((@Law2894.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2964 takes them (344 nodes). -/
def ordS7R12_Law2964 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2964. -/
theorem noS7R12_Law2964 : ∀ v : Magma.tup7R12,
    ¬ @Equation2964 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2964) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2964) (by native_decide) v.1 v.2
    ((@Law2964.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srch7R12_refutes_29 :
    FamilyRefutes Magma.srch7R12 [
      2850, 2858, 2868, 2875, 2876, 2878, 2880, 2886, 2890, 2894, 2964
    ] :=
  ⟨noS7R12_Law2850, noS7R12_Law2858, noS7R12_Law2868, noS7R12_Law2875, noS7R12_Law2876, noS7R12_Law2878, noS7R12_Law2880, noS7R12_Law2886, noS7R12_Law2890, noS7R12_Law2894, noS7R12_Law2964⟩
