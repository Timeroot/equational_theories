import equational_theories.Definability.Srch_S9R403

/-!
# Structural certificate targets: `Magma.srch9R403` (part 3 of 4)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S9R403_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 3,392 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S9R403_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2254 takes them (427 nodes). -/
def ordS9R403_Law2254 : List (Fin 7) := [0, 5, 1, 3, 4, 6, 2]

/-- No member of the class satisfies equation 2254. -/
theorem noS9R403_Law2254 : ∀ v : Magma.tup9R403,
    ¬ @Equation2254 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2254) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law2254) (by native_decide) v.1 v.2
    ((@Law2254.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2267 takes them (314 nodes). -/
def ordS9R403_Law2267 : List (Fin 7) := [5, 3, 1, 6, 0, 2, 4]

/-- No member of the class satisfies equation 2267. -/
theorem noS9R403_Law2267 : ∀ v : Magma.tup9R403,
    ¬ @Equation2267 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2267) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law2267) (by native_decide) v.1 v.2
    ((@Law2267.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2457 takes them (146 nodes). -/
def ordS9R403_Law2457 : List (Fin 7) := [1, 5, 0, 6, 2, 3, 4]

/-- No member of the class satisfies equation 2457. -/
theorem noS9R403_Law2457 : ∀ v : Magma.tup9R403,
    ¬ @Equation2457 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2457) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law2457) (by native_decide) v.1 v.2
    ((@Law2457.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2470 takes them (239 nodes). -/
def ordS9R403_Law2470 : List (Fin 7) := [6, 5, 1, 4, 0, 2, 3]

/-- No member of the class satisfies equation 2470. -/
theorem noS9R403_Law2470 : ∀ v : Magma.tup9R403,
    ¬ @Equation2470 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2470) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law2470) (by native_decide) v.1 v.2
    ((@Law2470.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2485 takes them (336 nodes). -/
def ordS9R403_Law2485 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2485. -/
theorem noS9R403_Law2485 : ∀ v : Magma.tup9R403,
    ¬ @Equation2485 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2850 takes them (185 nodes). -/
def ordS9R403_Law2850 : List (Fin 7) := [0, 2, 3, 6, 1, 4, 5]

/-- No member of the class satisfies equation 2850. -/
theorem noS9R403_Law2850 : ∀ v : Magma.tup9R403,
    ¬ @Equation2850 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2850) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law2850) (by native_decide) v.1 v.2
    ((@Law2850.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (350 nodes). -/
def ordS9R403_Law3053 : List (Fin 7) := [2, 6, 4, 5, 1, 0, 3]

/-- No member of the class satisfies equation 3053. -/
theorem noS9R403_Law3053 : ∀ v : Magma.tup9R403,
    ¬ @Equation3053 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3056 takes them (166 nodes). -/
def ordS9R403_Law3056 : List (Fin 7) := [0, 3, 6, 5, 2, 4, 1]

/-- No member of the class satisfies equation 3056. -/
theorem noS9R403_Law3056 : ∀ v : Magma.tup9R403,
    ¬ @Equation3056 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3056) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law3056) (by native_decide) v.1 v.2
    ((@Law3056.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (126 nodes). -/
def ordS9R403_Law3066 : List (Fin 7) := [0, 2, 6, 5, 1, 4, 3]

/-- No member of the class satisfies equation 3066. -/
theorem noS9R403_Law3066 : ∀ v : Magma.tup9R403,
    ¬ @Equation3066 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3079 takes them (238 nodes). -/
def ordS9R403_Law3079 : List (Fin 7) := [4, 5, 6, 1, 2, 0, 3]

/-- No member of the class satisfies equation 3079. -/
theorem noS9R403_Law3079 : ∀ v : Magma.tup9R403,
    ¬ @Equation3079 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3079) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 2)
    (ord := ordS9R403_Law3079) (by native_decide) v.1 v.2
    ((@Law3079.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (336 nodes). -/
def ordS9R403_Law3083 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3083. -/
theorem noS9R403_Law3083 : ∀ v : Magma.tup9R403,
    ¬ @Equation3083 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (336 nodes). -/
def ordS9R403_Law3094 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3094. -/
theorem noS9R403_Law3094 : ∀ v : Magma.tup9R403,
    ¬ @Equation3094 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3334 takes them (193 nodes). -/
def ordS9R403_Law3334 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3334. -/
theorem noS9R403_Law3334 : ∀ v : Magma.tup9R403,
    ¬ @Equation3334 (Fin 9) (Magma.srch9R403 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3334) (E := S9R403.E) (tr := S9R403.tr) (z := S9R403.z)
    (st := S9R403.st) (X := S9R403.X) (envs := Magma.envsRed 9 S9R403.E 3)
    (ord := ordS9R403_Law3334) (by native_decide) v.1 v.2
    ((@Law3334.models_iff (Fin 9) (Magma.srch9R403 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch9R403_refutes_2 :
    FamilyRefutes Magma.srch9R403 [
      2254, 2267, 2457, 2470, 2485, 2850, 3053, 3056, 3066, 3079, 3083, 3094, 3334
    ] :=
  ⟨noS9R403_Law2254, noS9R403_Law2267, noS9R403_Law2457, noS9R403_Law2470, noS9R403_Law2485, noS9R403_Law2850, noS9R403_Law3053, noS9R403_Law3056, noS9R403_Law3066, noS9R403_Law3079, noS9R403_Law3083, noS9R403_Law3094, noS9R403_Law3334⟩
