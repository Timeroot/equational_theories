import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 52 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 201 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4261 takes them (26 nodes). -/
def ordS6A_Law4261 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4261. -/
theorem noS6A_Law4261 : ∀ v : Magma.tupS6A,
    ¬ @Equation4261 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4261) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4261) (by native_decide) v.1 v.2
    ((@Law4261.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4262 takes them (24 nodes). -/
def ordS6A_Law4262 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4262. -/
theorem noS6A_Law4262 : ∀ v : Magma.tupS6A,
    ¬ @Equation4262 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4262) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4262) (by native_decide) v.1 v.2
    ((@Law4262.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4263 takes them (63 nodes). -/
def ordS6A_Law4263 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4263. -/
theorem noS6A_Law4263 : ∀ v : Magma.tupS6A,
    ¬ @Equation4263 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4263) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4263) (by native_decide) v.1 v.2
    ((@Law4263.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4264 takes them (22 nodes). -/
def ordS6A_Law4264 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4264. -/
theorem noS6A_Law4264 : ∀ v : Magma.tupS6A,
    ¬ @Equation4264 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4264) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4264) (by native_decide) v.1 v.2
    ((@Law4264.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4265 takes them (22 nodes). -/
def ordS6A_Law4265 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4265. -/
theorem noS6A_Law4265 : ∀ v : Magma.tupS6A,
    ¬ @Equation4265 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4265) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4265) (by native_decide) v.1 v.2
    ((@Law4265.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4266 takes them (22 nodes). -/
def ordS6A_Law4266 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4266. -/
theorem noS6A_Law4266 : ∀ v : Magma.tupS6A,
    ¬ @Equation4266 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4266) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 5)
    (ord := ordS6A_Law4266) (by native_decide) v.1 v.2
    ((@Law4266.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4267 takes them (22 nodes). -/
def ordS6A_Law4267 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 4267. -/
theorem noS6A_Law4267 : ∀ v : Magma.tupS6A,
    ¬ @Equation4267 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4267) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 6)
    (ord := ordS6A_Law4267) (by native_decide) v.1 v.2
    ((@Law4267.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch6A_refutes_51 :
    FamilyRefutes Magma.srch6A [
      4261, 4262, 4263, 4264, 4265, 4266, 4267
    ] :=
  ⟨noS6A_Law4261, noS6A_Law4262, noS6A_Law4263, noS6A_Law4264, noS6A_Law4265, noS6A_Law4266, noS6A_Law4267⟩
