import equational_theories.Definability.Srch_S9R322

/-!
# Structural certificate targets: `Magma.srch9R322` (part 2 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R322_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `77` equations here, 306 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R322_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2485 takes them (4 nodes). -/
def ordS9R322_Law2485 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2485. -/
theorem noS9R322_Law2485 : ∀ v : Magma.tup9R322,
    ¬ @Equation2485 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2496 takes them (4 nodes). -/
def ordS9R322_Law2496 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2496. -/
theorem noS9R322_Law2496 : ∀ v : Magma.tup9R322,
    ¬ @Equation2496 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2496) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2496) (by native_decide) v.1 v.2
    ((@Law2496.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2540 takes them (4 nodes). -/
def ordS9R322_Law2540 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2540. -/
theorem noS9R322_Law2540 : ∀ v : Magma.tup9R322,
    ¬ @Equation2540 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2540) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2540) (by native_decide) v.1 v.2
    ((@Law2540.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2653 takes them (4 nodes). -/
def ordS9R322_Law2653 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2653. -/
theorem noS9R322_Law2653 : ∀ v : Magma.tup9R322,
    ¬ @Equation2653 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2653) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2653) (by native_decide) v.1 v.2
    ((@Law2653.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2663 takes them (4 nodes). -/
def ordS9R322_Law2663 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2663. -/
theorem noS9R322_Law2663 : ∀ v : Magma.tup9R322,
    ¬ @Equation2663 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2663) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2663) (by native_decide) v.1 v.2
    ((@Law2663.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2672 takes them (5 nodes). -/
def ordS9R322_Law2672 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2672. -/
theorem noS9R322_Law2672 : ∀ v : Magma.tup9R322,
    ¬ @Equation2672 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2672) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2672) (by native_decide) v.1 v.2
    ((@Law2672.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2709 takes them (4 nodes). -/
def ordS9R322_Law2709 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2709. -/
theorem noS9R322_Law2709 : ∀ v : Magma.tup9R322,
    ¬ @Equation2709 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2709) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2709) (by native_decide) v.1 v.2
    ((@Law2709.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2736 takes them (4 nodes). -/
def ordS9R322_Law2736 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2736. -/
theorem noS9R322_Law2736 : ∀ v : Magma.tup9R322,
    ¬ @Equation2736 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2736) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2736) (by native_decide) v.1 v.2
    ((@Law2736.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2743 takes them (4 nodes). -/
def ordS9R322_Law2743 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2743. -/
theorem noS9R322_Law2743 : ∀ v : Magma.tup9R322,
    ¬ @Equation2743 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2743) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2743) (by native_decide) v.1 v.2
    ((@Law2743.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (4 nodes). -/
def ordS9R322_Law2850 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2850. -/
theorem noS9R322_Law2850 : ∀ v : Magma.tup9R322,
    ¬ @Equation2850 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2863 takes them (4 nodes). -/
def ordS9R322_Law2863 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2863. -/
theorem noS9R322_Law2863 : ∀ v : Magma.tup9R322,
    ¬ @Equation2863 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2863) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2863) (by native_decide) v.1 v.2
    ((@Law2863.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2875 takes them (5 nodes). -/
def ordS9R322_Law2875 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2875. -/
theorem noS9R322_Law2875 : ∀ v : Magma.tup9R322,
    ¬ @Equation2875 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2875) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2875) (by native_decide) v.1 v.2
    ((@Law2875.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2902 takes them (4 nodes). -/
def ordS9R322_Law2902 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2902. -/
theorem noS9R322_Law2902 : ∀ v : Magma.tup9R322,
    ¬ @Equation2902 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2902) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2902) (by native_decide) v.1 v.2
    ((@Law2902.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2909 takes them (4 nodes). -/
def ordS9R322_Law2909 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2909. -/
theorem noS9R322_Law2909 : ∀ v : Magma.tup9R322,
    ¬ @Equation2909 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2909) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2909) (by native_decide) v.1 v.2
    ((@Law2909.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2936 takes them (4 nodes). -/
def ordS9R322_Law2936 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 2936. -/
theorem noS9R322_Law2936 : ∀ v : Magma.tup9R322,
    ¬ @Equation2936 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2936) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law2936) (by native_decide) v.1 v.2
    ((@Law2936.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (4 nodes). -/
def ordS9R322_Law3053 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3053. -/
theorem noS9R322_Law3053 : ∀ v : Magma.tup9R322,
    ¬ @Equation3053 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3058 takes them (5 nodes). -/
def ordS9R322_Law3058 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3058. -/
theorem noS9R322_Law3058 : ∀ v : Magma.tup9R322,
    ¬ @Equation3058 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3058) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3058) (by native_decide) v.1 v.2
    ((@Law3058.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (4 nodes). -/
def ordS9R322_Law3066 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3066. -/
theorem noS9R322_Law3066 : ∀ v : Magma.tup9R322,
    ¬ @Equation3066 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3075 takes them (5 nodes). -/
def ordS9R322_Law3075 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3075. -/
theorem noS9R322_Law3075 : ∀ v : Magma.tup9R322,
    ¬ @Equation3075 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3075) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3075) (by native_decide) v.1 v.2
    ((@Law3075.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (4 nodes). -/
def ordS9R322_Law3083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3083. -/
theorem noS9R322_Law3083 : ∀ v : Magma.tup9R322,
    ¬ @Equation3083 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (4 nodes). -/
def ordS9R322_Law3094 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3094. -/
theorem noS9R322_Law3094 : ∀ v : Magma.tup9R322,
    ¬ @Equation3094 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3112 takes them (4 nodes). -/
def ordS9R322_Law3112 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3112. -/
theorem noS9R322_Law3112 : ∀ v : Magma.tup9R322,
    ¬ @Equation3112 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3112) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3112) (by native_decide) v.1 v.2
    ((@Law3112.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (4 nodes). -/
def ordS9R322_Law3142 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3142. -/
theorem noS9R322_Law3142 : ∀ v : Magma.tup9R322,
    ¬ @Equation3142 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3259 takes them (4 nodes). -/
def ordS9R322_Law3259 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3259. -/
theorem noS9R322_Law3259 : ∀ v : Magma.tup9R322,
    ¬ @Equation3259 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3259) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3259) (by native_decide) v.1 v.2
    ((@Law3259.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3261 takes them (5 nodes). -/
def ordS9R322_Law3261 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3261. -/
theorem noS9R322_Law3261 : ∀ v : Magma.tup9R322,
    ¬ @Equation3261 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3261) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3261) (by native_decide) v.1 v.2
    ((@Law3261.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3278 takes them (4 nodes). -/
def ordS9R322_Law3278 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3278. -/
theorem noS9R322_Law3278 : ∀ v : Magma.tup9R322,
    ¬ @Equation3278 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3278) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3278) (by native_decide) v.1 v.2
    ((@Law3278.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3306 takes them (5 nodes). -/
def ordS9R322_Law3306 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3306. -/
theorem noS9R322_Law3306 : ∀ v : Magma.tup9R322,
    ¬ @Equation3306 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3306) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3306) (by native_decide) v.1 v.2
    ((@Law3306.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (5 nodes). -/
def ordS9R322_Law3334 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3334. -/
theorem noS9R322_Law3334 : ∀ v : Magma.tup9R322,
    ¬ @Equation3334 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3342 takes them (3 nodes). -/
def ordS9R322_Law3342 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3342. -/
theorem noS9R322_Law3342 : ∀ v : Magma.tup9R322,
    ¬ @Equation3342 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3342) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3342) (by native_decide) v.1 v.2
    ((@Law3342.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3353 takes them (4 nodes). -/
def ordS9R322_Law3353 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3353. -/
theorem noS9R322_Law3353 : ∀ v : Magma.tup9R322,
    ¬ @Equation3353 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3353) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3353) (by native_decide) v.1 v.2
    ((@Law3353.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3414 takes them (4 nodes). -/
def ordS9R322_Law3414 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3414. -/
theorem noS9R322_Law3414 : ∀ v : Magma.tup9R322,
    ¬ @Equation3414 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3414) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law3414) (by native_decide) v.1 v.2
    ((@Law3414.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3459 takes them (4 nodes). -/
def ordS9R322_Law3459 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3459. -/
theorem noS9R322_Law3459 : ∀ v : Magma.tup9R322,
    ¬ @Equation3459 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3459) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3459) (by native_decide) v.1 v.2
    ((@Law3459.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3462 takes them (4 nodes). -/
def ordS9R322_Law3462 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3462. -/
theorem noS9R322_Law3462 : ∀ v : Magma.tup9R322,
    ¬ @Equation3462 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3462) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3462) (by native_decide) v.1 v.2
    ((@Law3462.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3484 takes them (4 nodes). -/
def ordS9R322_Law3484 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3484. -/
theorem noS9R322_Law3484 : ∀ v : Magma.tup9R322,
    ¬ @Equation3484 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3484) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3484) (by native_decide) v.1 v.2
    ((@Law3484.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3518 takes them (4 nodes). -/
def ordS9R322_Law3518 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3518. -/
theorem noS9R322_Law3518 : ∀ v : Magma.tup9R322,
    ¬ @Equation3518 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3518) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3518) (by native_decide) v.1 v.2
    ((@Law3518.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3526 takes them (4 nodes). -/
def ordS9R322_Law3526 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3526. -/
theorem noS9R322_Law3526 : ∀ v : Magma.tup9R322,
    ¬ @Equation3526 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3526) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law3526) (by native_decide) v.1 v.2
    ((@Law3526.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3545 takes them (3 nodes). -/
def ordS9R322_Law3545 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3545. -/
theorem noS9R322_Law3545 : ∀ v : Magma.tup9R322,
    ¬ @Equation3545 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3545) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3545) (by native_decide) v.1 v.2
    ((@Law3545.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3556 takes them (4 nodes). -/
def ordS9R322_Law3556 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3556. -/
theorem noS9R322_Law3556 : ∀ v : Magma.tup9R322,
    ¬ @Equation3556 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3556) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3556) (by native_decide) v.1 v.2
    ((@Law3556.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3668 takes them (4 nodes). -/
def ordS9R322_Law3668 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3668. -/
theorem noS9R322_Law3668 : ∀ v : Magma.tup9R322,
    ¬ @Equation3668 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3668) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3668) (by native_decide) v.1 v.2
    ((@Law3668.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3687 takes them (4 nodes). -/
def ordS9R322_Law3687 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3687. -/
theorem noS9R322_Law3687 : ∀ v : Magma.tup9R322,
    ¬ @Equation3687 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3687) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3687) (by native_decide) v.1 v.2
    ((@Law3687.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3724 takes them (4 nodes). -/
def ordS9R322_Law3724 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3724. -/
theorem noS9R322_Law3724 : ∀ v : Magma.tup9R322,
    ¬ @Equation3724 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3724) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3724) (by native_decide) v.1 v.2
    ((@Law3724.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3749 takes them (4 nodes). -/
def ordS9R322_Law3749 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3749. -/
theorem noS9R322_Law3749 : ∀ v : Magma.tup9R322,
    ¬ @Equation3749 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3749) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3749) (by native_decide) v.1 v.2
    ((@Law3749.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3751 takes them (3 nodes). -/
def ordS9R322_Law3751 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3751. -/
theorem noS9R322_Law3751 : ∀ v : Magma.tup9R322,
    ¬ @Equation3751 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3751) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3751) (by native_decide) v.1 v.2
    ((@Law3751.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3758 takes them (3 nodes). -/
def ordS9R322_Law3758 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3758. -/
theorem noS9R322_Law3758 : ∀ v : Magma.tup9R322,
    ¬ @Equation3758 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3758) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3758) (by native_decide) v.1 v.2
    ((@Law3758.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3871 takes them (4 nodes). -/
def ordS9R322_Law3871 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3871. -/
theorem noS9R322_Law3871 : ∀ v : Magma.tup9R322,
    ¬ @Equation3871 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3871) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3871) (by native_decide) v.1 v.2
    ((@Law3871.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3880 takes them (4 nodes). -/
def ordS9R322_Law3880 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3880. -/
theorem noS9R322_Law3880 : ∀ v : Magma.tup9R322,
    ¬ @Equation3880 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3880) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3880) (by native_decide) v.1 v.2
    ((@Law3880.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3887 takes them (4 nodes). -/
def ordS9R322_Law3887 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3887. -/
theorem noS9R322_Law3887 : ∀ v : Magma.tup9R322,
    ¬ @Equation3887 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3887) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3887) (by native_decide) v.1 v.2
    ((@Law3887.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3924 takes them (4 nodes). -/
def ordS9R322_Law3924 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3924. -/
theorem noS9R322_Law3924 : ∀ v : Magma.tup9R322,
    ¬ @Equation3924 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3924) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3924) (by native_decide) v.1 v.2
    ((@Law3924.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3962 takes them (4 nodes). -/
def ordS9R322_Law3962 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3962. -/
theorem noS9R322_Law3962 : ∀ v : Magma.tup9R322,
    ¬ @Equation3962 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3962) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3962) (by native_decide) v.1 v.2
    ((@Law3962.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3964 takes them (3 nodes). -/
def ordS9R322_Law3964 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 3964. -/
theorem noS9R322_Law3964 : ∀ v : Magma.tup9R322,
    ¬ @Equation3964 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3964) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law3964) (by native_decide) v.1 v.2
    ((@Law3964.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4023 takes them (4 nodes). -/
def ordS9R322_Law4023 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4023. -/
theorem noS9R322_Law4023 : ∀ v : Magma.tup9R322,
    ¬ @Equation4023 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4023) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4023) (by native_decide) v.1 v.2
    ((@Law4023.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4068 takes them (4 nodes). -/
def ordS9R322_Law4068 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4068. -/
theorem noS9R322_Law4068 : ∀ v : Magma.tup9R322,
    ¬ @Equation4068 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4068) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4068) (by native_decide) v.1 v.2
    ((@Law4068.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4073 takes them (5 nodes). -/
def ordS9R322_Law4073 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4073. -/
theorem noS9R322_Law4073 : ∀ v : Magma.tup9R322,
    ¬ @Equation4073 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4073) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4073) (by native_decide) v.1 v.2
    ((@Law4073.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4083 takes them (4 nodes). -/
def ordS9R322_Law4083 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4083. -/
theorem noS9R322_Law4083 : ∀ v : Magma.tup9R322,
    ¬ @Equation4083 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4083) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4083) (by native_decide) v.1 v.2
    ((@Law4083.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4127 takes them (4 nodes). -/
def ordS9R322_Law4127 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4127. -/
theorem noS9R322_Law4127 : ∀ v : Magma.tup9R322,
    ¬ @Equation4127 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4127) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4127) (by native_decide) v.1 v.2
    ((@Law4127.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4131 takes them (5 nodes). -/
def ordS9R322_Law4131 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4131. -/
theorem noS9R322_Law4131 : ∀ v : Magma.tup9R322,
    ¬ @Equation4131 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4131) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4131) (by native_decide) v.1 v.2
    ((@Law4131.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4135 takes them (4 nodes). -/
def ordS9R322_Law4135 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4135. -/
theorem noS9R322_Law4135 : ∀ v : Magma.tup9R322,
    ¬ @Equation4135 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4135) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4135) (by native_decide) v.1 v.2
    ((@Law4135.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4146 takes them (5 nodes). -/
def ordS9R322_Law4146 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4146. -/
theorem noS9R322_Law4146 : ∀ v : Magma.tup9R322,
    ¬ @Equation4146 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4146) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4146) (by native_decide) v.1 v.2
    ((@Law4146.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4167 takes them (3 nodes). -/
def ordS9R322_Law4167 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4167. -/
theorem noS9R322_Law4167 : ∀ v : Magma.tup9R322,
    ¬ @Equation4167 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4167) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4167) (by native_decide) v.1 v.2
    ((@Law4167.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4275 takes them (4 nodes). -/
def ordS9R322_Law4275 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4275. -/
theorem noS9R322_Law4275 : ∀ v : Magma.tup9R322,
    ¬ @Equation4275 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4275) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4275) (by native_decide) v.1 v.2
    ((@Law4275.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4283 takes them (4 nodes). -/
def ordS9R322_Law4283 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4283. -/
theorem noS9R322_Law4283 : ∀ v : Magma.tup9R322,
    ¬ @Equation4283 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4283) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4283) (by native_decide) v.1 v.2
    ((@Law4283.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4307 takes them (4 nodes). -/
def ordS9R322_Law4307 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4307. -/
theorem noS9R322_Law4307 : ∀ v : Magma.tup9R322,
    ¬ @Equation4307 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4307) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4307) (by native_decide) v.1 v.2
    ((@Law4307.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4343 takes them (3 nodes). -/
def ordS9R322_Law4343 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4343. -/
theorem noS9R322_Law4343 : ∀ v : Magma.tup9R322,
    ¬ @Equation4343 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4343) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4343) (by native_decide) v.1 v.2
    ((@Law4343.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4358 takes them (4 nodes). -/
def ordS9R322_Law4358 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4358. -/
theorem noS9R322_Law4358 : ∀ v : Magma.tup9R322,
    ¬ @Equation4358 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4358) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4358) (by native_decide) v.1 v.2
    ((@Law4358.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4383 takes them (4 nodes). -/
def ordS9R322_Law4383 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4383. -/
theorem noS9R322_Law4383 : ∀ v : Magma.tup9R322,
    ¬ @Equation4383 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4383) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4383) (by native_decide) v.1 v.2
    ((@Law4383.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4398 takes them (4 nodes). -/
def ordS9R322_Law4398 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4398. -/
theorem noS9R322_Law4398 : ∀ v : Magma.tup9R322,
    ¬ @Equation4398 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4398) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4398) (by native_decide) v.1 v.2
    ((@Law4398.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4405 takes them (3 nodes). -/
def ordS9R322_Law4405 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4405. -/
theorem noS9R322_Law4405 : ∀ v : Magma.tup9R322,
    ¬ @Equation4405 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4405) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4405) (by native_decide) v.1 v.2
    ((@Law4405.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4409 takes them (4 nodes). -/
def ordS9R322_Law4409 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4409. -/
theorem noS9R322_Law4409 : ∀ v : Magma.tup9R322,
    ¬ @Equation4409 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4409) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4409) (by native_decide) v.1 v.2
    ((@Law4409.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4442 takes them (4 nodes). -/
def ordS9R322_Law4442 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4442. -/
theorem noS9R322_Law4442 : ∀ v : Magma.tup9R322,
    ¬ @Equation4442 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4442) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4442) (by native_decide) v.1 v.2
    ((@Law4442.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4482 takes them (3 nodes). -/
def ordS9R322_Law4482 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4482. -/
theorem noS9R322_Law4482 : ∀ v : Magma.tup9R322,
    ¬ @Equation4482 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4482) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4482) (by native_decide) v.1 v.2
    ((@Law4482.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4531 takes them (3 nodes). -/
def ordS9R322_Law4531 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4531. -/
theorem noS9R322_Law4531 : ∀ v : Magma.tup9R322,
    ¬ @Equation4531 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4531) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4531) (by native_decide) v.1 v.2
    ((@Law4531.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4544 takes them (3 nodes). -/
def ordS9R322_Law4544 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4544. -/
theorem noS9R322_Law4544 : ∀ v : Magma.tup9R322,
    ¬ @Equation4544 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4544) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4544) (by native_decide) v.1 v.2
    ((@Law4544.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4585 takes them (4 nodes). -/
def ordS9R322_Law4585 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4585. -/
theorem noS9R322_Law4585 : ∀ v : Magma.tup9R322,
    ¬ @Equation4585 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4585) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4585) (by native_decide) v.1 v.2
    ((@Law4585.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4608 takes them (3 nodes). -/
def ordS9R322_Law4608 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4608. -/
theorem noS9R322_Law4608 : ∀ v : Magma.tup9R322,
    ¬ @Equation4608 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4608) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4608) (by native_decide) v.1 v.2
    ((@Law4608.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4635 takes them (4 nodes). -/
def ordS9R322_Law4635 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4635. -/
theorem noS9R322_Law4635 : ∀ v : Magma.tup9R322,
    ¬ @Equation4635 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4635) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 2)
    (ord := ordS9R322_Law4635) (by native_decide) v.1 v.2
    ((@Law4635.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4656 takes them (4 nodes). -/
def ordS9R322_Law4656 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4656. -/
theorem noS9R322_Law4656 : ∀ v : Magma.tup9R322,
    ¬ @Equation4656 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4656) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4656) (by native_decide) v.1 v.2
    ((@Law4656.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4677 takes them (4 nodes). -/
def ordS9R322_Law4677 : List (Fin 2) := [0, 1]

/-- No member of the class satisfies equation 4677. -/
theorem noS9R322_Law4677 : ∀ v : Magma.tup9R322,
    ¬ @Equation4677 (Fin 9) (Magma.srch9R322 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4677) (E := S9R322.E) (tr := S9R322.tr) (z := S9R322.z)
    (st := S9R322.st) (X := S9R322.X) (envs := Magma.envsRed 9 S9R322.E 3)
    (ord := ordS9R322_Law4677) (by native_decide) v.1 v.2
    ((@Law4677.models_iff (Fin 9) (Magma.srch9R322 v)).mpr hv)

/-- No member of the class satisfies any of these `77` equations. -/
theorem srch9R322_refutes_1 :
    FamilyRefutes Magma.srch9R322 [
      2485, 2496, 2540, 2653, 2663, 2672, 2709, 2736, 2743, 2850, 2863, 2875, 2902, 2909, 2936,
      3053, 3058, 3066, 3075, 3083, 3094, 3112, 3142, 3259, 3261, 3278, 3306, 3334, 3342, 3353,
      3414, 3459, 3462, 3484, 3518, 3526, 3545, 3556, 3668, 3687, 3724, 3749, 3751, 3758, 3871,
      3880, 3887, 3924, 3962, 3964, 4023, 4068, 4073, 4083, 4127, 4131, 4135, 4146, 4167, 4275,
      4283, 4307, 4343, 4358, 4383, 4398, 4405, 4409, 4442, 4482, 4531, 4544, 4585, 4608, 4635,
      4656, 4677
    ] :=
  ⟨noS9R322_Law2485, noS9R322_Law2496, noS9R322_Law2540, noS9R322_Law2653, noS9R322_Law2663, noS9R322_Law2672, noS9R322_Law2709, noS9R322_Law2736, noS9R322_Law2743, noS9R322_Law2850, noS9R322_Law2863, noS9R322_Law2875, noS9R322_Law2902, noS9R322_Law2909, noS9R322_Law2936, noS9R322_Law3053, noS9R322_Law3058, noS9R322_Law3066, noS9R322_Law3075, noS9R322_Law3083, noS9R322_Law3094, noS9R322_Law3112, noS9R322_Law3142, noS9R322_Law3259, noS9R322_Law3261, noS9R322_Law3278, noS9R322_Law3306, noS9R322_Law3334, noS9R322_Law3342, noS9R322_Law3353, noS9R322_Law3414, noS9R322_Law3459, noS9R322_Law3462, noS9R322_Law3484, noS9R322_Law3518, noS9R322_Law3526, noS9R322_Law3545, noS9R322_Law3556, noS9R322_Law3668, noS9R322_Law3687, noS9R322_Law3724, noS9R322_Law3749, noS9R322_Law3751, noS9R322_Law3758, noS9R322_Law3871, noS9R322_Law3880, noS9R322_Law3887, noS9R322_Law3924, noS9R322_Law3962, noS9R322_Law3964, noS9R322_Law4023, noS9R322_Law4068, noS9R322_Law4073, noS9R322_Law4083, noS9R322_Law4127, noS9R322_Law4131, noS9R322_Law4135, noS9R322_Law4146, noS9R322_Law4167, noS9R322_Law4275, noS9R322_Law4283, noS9R322_Law4307, noS9R322_Law4343, noS9R322_Law4358, noS9R322_Law4383, noS9R322_Law4398, noS9R322_Law4405, noS9R322_Law4409, noS9R322_Law4442, noS9R322_Law4482, noS9R322_Law4531, noS9R322_Law4544, noS9R322_Law4585, noS9R322_Law4608, noS9R322_Law4635, noS9R322_Law4656, noS9R322_Law4677⟩
