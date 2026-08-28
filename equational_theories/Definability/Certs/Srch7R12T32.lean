import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 33 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `12` equations here, 3,101 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 3093 takes them (200 nodes). -/
def ordS7R12_Law3093 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3093. -/
theorem noS7R12_Law3093 : ∀ v : Magma.tup7R12,
    ¬ @Equation3093 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3093) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3093) (by native_decide) v.1 v.2
    ((@Law3093.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (430 nodes). -/
def ordS7R12_Law3094 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3094. -/
theorem noS7R12_Law3094 : ∀ v : Magma.tup7R12,
    ¬ @Equation3094 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3097 takes them (141 nodes). -/
def ordS7R12_Law3097 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3097. -/
theorem noS7R12_Law3097 : ∀ v : Magma.tup7R12,
    ¬ @Equation3097 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3097) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3097) (by native_decide) v.1 v.2
    ((@Law3097.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3142 takes them (664 nodes). -/
def ordS7R12_Law3142 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3142. -/
theorem noS7R12_Law3142 : ∀ v : Magma.tup7R12,
    ¬ @Equation3142 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3142) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3142) (by native_decide) v.1 v.2
    ((@Law3142.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3180 takes them (119 nodes). -/
def ordS7R12_Law3180 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3180. -/
theorem noS7R12_Law3180 : ∀ v : Magma.tup7R12,
    ¬ @Equation3180 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3180) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3180) (by native_decide) v.1 v.2
    ((@Law3180.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3214 takes them (428 nodes). -/
def ordS7R12_Law3214 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3214. -/
theorem noS7R12_Law3214 : ∀ v : Magma.tup7R12,
    ¬ @Equation3214 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3214) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3214) (by native_decide) v.1 v.2
    ((@Law3214.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3265 takes them (191 nodes). -/
def ordS7R12_Law3265 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3265. -/
theorem noS7R12_Law3265 : ∀ v : Magma.tup7R12,
    ¬ @Equation3265 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3265) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3265) (by native_decide) v.1 v.2
    ((@Law3265.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3267 takes them (38 nodes). -/
def ordS7R12_Law3267 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3267. -/
theorem noS7R12_Law3267 : ∀ v : Magma.tup7R12,
    ¬ @Equation3267 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3267) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3267) (by native_decide) v.1 v.2
    ((@Law3267.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3274 takes them (185 nodes). -/
def ordS7R12_Law3274 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3274. -/
theorem noS7R12_Law3274 : ∀ v : Magma.tup7R12,
    ¬ @Equation3274 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3274) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3274) (by native_decide) v.1 v.2
    ((@Law3274.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3290 takes them (163 nodes). -/
def ordS7R12_Law3290 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3290. -/
theorem noS7R12_Law3290 : ∀ v : Magma.tup7R12,
    ¬ @Equation3290 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3290) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law3290) (by native_decide) v.1 v.2
    ((@Law3290.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3302 takes them (154 nodes). -/
def ordS7R12_Law3302 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3302. -/
theorem noS7R12_Law3302 : ∀ v : Magma.tup7R12,
    ¬ @Equation3302 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3302) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law3302) (by native_decide) v.1 v.2
    ((@Law3302.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3308 takes them (388 nodes). -/
def ordS7R12_Law3308 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 3308. -/
theorem noS7R12_Law3308 : ∀ v : Magma.tup7R12,
    ¬ @Equation3308 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3308) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 2)
    (ord := ordS7R12_Law3308) (by native_decide) v.1 v.2
    ((@Law3308.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `12` equations. -/
theorem srch7R12_refutes_32 :
    FamilyRefutes Magma.srch7R12 [
      3093, 3094, 3097, 3142, 3180, 3214, 3265, 3267, 3274, 3290, 3302, 3308
    ] :=
  ⟨noS7R12_Law3093, noS7R12_Law3094, noS7R12_Law3097, noS7R12_Law3142, noS7R12_Law3180, noS7R12_Law3214, noS7R12_Law3265, noS7R12_Law3267, noS7R12_Law3274, noS7R12_Law3290, noS7R12_Law3302, noS7R12_Law3308⟩
