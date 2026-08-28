import equational_theories.Definability.Srch_S8R66

/-!
# Structural certificate targets: `Magma.srch8R66` (part 7 of 8)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R66_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,236 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R66_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2647 takes them (227 nodes). -/
def ordS8R66_Law2647 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2647. -/
theorem noS8R66_Law2647 : ∀ v : Magma.tup8R66,
    ¬ @Equation2647 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2647) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2647) (by native_decide) v.1 v.2
    ((@Law2647.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2660 takes them (213 nodes). -/
def ordS8R66_Law2660 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2660. -/
theorem noS8R66_Law2660 : ∀ v : Magma.tup8R66,
    ¬ @Equation2660 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2660) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2660) (by native_decide) v.1 v.2
    ((@Law2660.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2673 takes them (91 nodes). -/
def ordS8R66_Law2673 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2673. -/
theorem noS8R66_Law2673 : ∀ v : Magma.tup8R66,
    ¬ @Equation2673 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2673) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2673) (by native_decide) v.1 v.2
    ((@Law2673.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2688 takes them (77 nodes). -/
def ordS8R66_Law2688 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2688. -/
theorem noS8R66_Law2688 : ∀ v : Magma.tup8R66,
    ¬ @Equation2688 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2688) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law2688) (by native_decide) v.1 v.2
    ((@Law2688.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (451 nodes). -/
def ordS8R66_Law2850 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2850. -/
theorem noS8R66_Law2850 : ∀ v : Magma.tup8R66,
    ¬ @Equation2850 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2876 takes them (97 nodes). -/
def ordS8R66_Law2876 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2876. -/
theorem noS8R66_Law2876 : ∀ v : Magma.tup8R66,
    ¬ @Equation2876 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2876) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law2876) (by native_decide) v.1 v.2
    ((@Law2876.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2880 takes them (77 nodes). -/
def ordS8R66_Law2880 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2880. -/
theorem noS8R66_Law2880 : ∀ v : Magma.tup8R66,
    ¬ @Equation2880 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2880) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law2880) (by native_decide) v.1 v.2
    ((@Law2880.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (693 nodes). -/
def ordS8R66_Law3053 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3053. -/
theorem noS8R66_Law3053 : ∀ v : Magma.tup8R66,
    ¬ @Equation3053 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (317 nodes). -/
def ordS8R66_Law3066 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3066. -/
theorem noS8R66_Law3066 : ∀ v : Magma.tup8R66,
    ¬ @Equation3066 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3079 takes them (395 nodes). -/
def ordS8R66_Law3079 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3079. -/
theorem noS8R66_Law3079 : ∀ v : Magma.tup8R66,
    ¬ @Equation3079 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3079) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 2)
    (ord := ordS8R66_Law3079) (by native_decide) v.1 v.2
    ((@Law3079.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (299 nodes). -/
def ordS8R66_Law3083 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3083. -/
theorem noS8R66_Law3083 : ∀ v : Magma.tup8R66,
    ¬ @Equation3083 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (299 nodes). -/
def ordS8R66_Law3094 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 3094. -/
theorem noS8R66_Law3094 : ∀ v : Magma.tup8R66,
    ¬ @Equation3094 (Fin 8) (Magma.srch8R66 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S8R66.E) (tr := S8R66.tr) (z := S8R66.z)
    (st := S8R66.st) (X := S8R66.X) (envs := Magma.envsRed 8 S8R66.E 3)
    (ord := ordS8R66_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 8) (Magma.srch8R66 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch8R66_refutes_6 :
    FamilyRefutes Magma.srch8R66 [
      2647, 2660, 2673, 2688, 2850, 2876, 2880, 3053, 3066, 3079, 3083, 3094
    ] :=
  ⟨noS8R66_Law2647, noS8R66_Law2660, noS8R66_Law2673, noS8R66_Law2688, noS8R66_Law2850, noS8R66_Law2876, noS8R66_Law2880, noS8R66_Law3053, noS8R66_Law3066, noS8R66_Law3079, noS8R66_Law3083, noS8R66_Law3094⟩
