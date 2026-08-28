import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 183 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `10`
equations here, 3,393 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3222 takes them (741 nodes). -/
def ordS8R9_Law3222 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3222. -/
theorem noS8R9_Law3222 : ∀ v : Magma.tup8R9,
    ¬ @Equation3222 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3222) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3222) (by native_decide) v.1 v.2
    ((@Law3222.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3232 takes them (15 nodes). -/
def ordS8R9_Law3232 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3232. -/
theorem noS8R9_Law3232 : ∀ v : Magma.tup8R9,
    ¬ @Equation3232 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3232) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3232) (by native_decide) v.1 v.2
    ((@Law3232.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3237 takes them (13 nodes). -/
def ordS8R9_Law3237 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3237. -/
theorem noS8R9_Law3237 : ∀ v : Magma.tup8R9,
    ¬ @Equation3237 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3237) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3237) (by native_decide) v.1 v.2
    ((@Law3237.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3242 takes them (741 nodes). -/
def ordS8R9_Law3242 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3242. -/
theorem noS8R9_Law3242 : ∀ v : Magma.tup8R9,
    ¬ @Equation3242 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3242) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3242) (by native_decide) v.1 v.2
    ((@Law3242.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3247 takes them (13 nodes). -/
def ordS8R9_Law3247 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3247. -/
theorem noS8R9_Law3247 : ∀ v : Magma.tup8R9,
    ¬ @Equation3247 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3247) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law3247) (by native_decide) v.1 v.2
    ((@Law3247.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3260 takes them (195 nodes). -/
def ordS8R9_Law3260 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3260. -/
theorem noS8R9_Law3260 : ∀ v : Magma.tup8R9,
    ¬ @Equation3260 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3260) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3260) (by native_decide) v.1 v.2
    ((@Law3260.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3263 takes them (769 nodes). -/
def ordS8R9_Law3263 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3263. -/
theorem noS8R9_Law3263 : ∀ v : Magma.tup8R9,
    ¬ @Equation3263 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3263) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3263) (by native_decide) v.1 v.2
    ((@Law3263.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3265 takes them (776 nodes). -/
def ordS8R9_Law3265 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3265. -/
theorem noS8R9_Law3265 : ∀ v : Magma.tup8R9,
    ¬ @Equation3265 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3265) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3265) (by native_decide) v.1 v.2
    ((@Law3265.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3266 takes them (65 nodes). -/
def ordS8R9_Law3266 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3266. -/
theorem noS8R9_Law3266 : ∀ v : Magma.tup8R9,
    ¬ @Equation3266 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3266) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law3266) (by native_decide) v.1 v.2
    ((@Law3266.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3267 takes them (65 nodes). -/
def ordS8R9_Law3267 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3267. -/
theorem noS8R9_Law3267 : ∀ v : Magma.tup8R9,
    ¬ @Equation3267 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3267) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law3267) (by native_decide) v.1 v.2
    ((@Law3267.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch8R9_refutes_182 :
    FamilyRefutes Magma.srch8R9 [
      3222, 3232, 3237, 3242, 3247, 3260, 3263, 3265, 3266, 3267
    ] :=
  ⟨noS8R9_Law3222, noS8R9_Law3232, noS8R9_Law3237, noS8R9_Law3242, noS8R9_Law3247, noS8R9_Law3260, noS8R9_Law3263, noS8R9_Law3265, noS8R9_Law3266, noS8R9_Law3267⟩
