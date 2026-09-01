import equational_theories.Definability.Srch_S7R325

/-!
# Structural certificate targets: `Magma.srch7R325` (part 8 of 25)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R325_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `17` equations here, 2,999 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R325_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 4281 takes them (10 nodes). -/
def ordS7R325_Law4281 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4281. -/
theorem noS7R325_Law4281 : ∀ v : Magma.tup7R325,
    ¬ @Equation4281 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4281) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4281) (by native_decide) v.1 v.2
    ((@Law4281.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4285 takes them (818 nodes). -/
def ordS7R325_Law4285 : List (Fin 9) := [5, 0, 1, 7, 4, 8, 6, 3, 2]

/-- No member of the class satisfies equation 4285. -/
theorem noS7R325_Law4285 : ∀ v : Magma.tup7R325,
    ¬ @Equation4285 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4285) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4285) (by native_decide) v.1 v.2
    ((@Law4285.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4287 takes them (716 nodes). -/
def ordS7R325_Law4287 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4287. -/
theorem noS7R325_Law4287 : ∀ v : Magma.tup7R325,
    ¬ @Equation4287 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4287) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4287) (by native_decide) v.1 v.2
    ((@Law4287.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4289 takes them (240 nodes). -/
def ordS7R325_Law4289 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4289. -/
theorem noS7R325_Law4289 : ∀ v : Magma.tup7R325,
    ¬ @Equation4289 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4289) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4289) (by native_decide) v.1 v.2
    ((@Law4289.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4292 takes them (151 nodes). -/
def ordS7R325_Law4292 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4292. -/
theorem noS7R325_Law4292 : ∀ v : Magma.tup7R325,
    ¬ @Equation4292 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4292) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4292) (by native_decide) v.1 v.2
    ((@Law4292.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4295 takes them (155 nodes). -/
def ordS7R325_Law4295 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4295. -/
theorem noS7R325_Law4295 : ∀ v : Magma.tup7R325,
    ¬ @Equation4295 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4295) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4295) (by native_decide) v.1 v.2
    ((@Law4295.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4298 takes them (10 nodes). -/
def ordS7R325_Law4298 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4298. -/
theorem noS7R325_Law4298 : ∀ v : Magma.tup7R325,
    ¬ @Equation4298 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4298) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4298) (by native_decide) v.1 v.2
    ((@Law4298.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4300 takes them (261 nodes). -/
def ordS7R325_Law4300 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4300. -/
theorem noS7R325_Law4300 : ∀ v : Magma.tup7R325,
    ¬ @Equation4300 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4300) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4300) (by native_decide) v.1 v.2
    ((@Law4300.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4302 takes them (10 nodes). -/
def ordS7R325_Law4302 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4302. -/
theorem noS7R325_Law4302 : ∀ v : Magma.tup7R325,
    ¬ @Equation4302 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4302) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4302) (by native_decide) v.1 v.2
    ((@Law4302.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4303 takes them (153 nodes). -/
def ordS7R325_Law4303 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4303. -/
theorem noS7R325_Law4303 : ∀ v : Magma.tup7R325,
    ¬ @Equation4303 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4303) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4303) (by native_decide) v.1 v.2
    ((@Law4303.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4306 takes them (10 nodes). -/
def ordS7R325_Law4306 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4306. -/
theorem noS7R325_Law4306 : ∀ v : Magma.tup7R325,
    ¬ @Equation4306 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4306) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4306) (by native_decide) v.1 v.2
    ((@Law4306.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4309 takes them (10 nodes). -/
def ordS7R325_Law4309 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4309. -/
theorem noS7R325_Law4309 : ∀ v : Magma.tup7R325,
    ¬ @Equation4309 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4309) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4309) (by native_decide) v.1 v.2
    ((@Law4309.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4310 takes them (58 nodes). -/
def ordS7R325_Law4310 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4310. -/
theorem noS7R325_Law4310 : ∀ v : Magma.tup7R325,
    ¬ @Equation4310 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4310) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4310) (by native_decide) v.1 v.2
    ((@Law4310.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4313 takes them (10 nodes). -/
def ordS7R325_Law4313 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4313. -/
theorem noS7R325_Law4313 : ∀ v : Magma.tup7R325,
    ¬ @Equation4313 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4313) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 5)
    (ord := ordS7R325_Law4313) (by native_decide) v.1 v.2
    ((@Law4313.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4317 takes them (199 nodes). -/
def ordS7R325_Law4317 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4317. -/
theorem noS7R325_Law4317 : ∀ v : Magma.tup7R325,
    ¬ @Equation4317 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4317) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4317) (by native_decide) v.1 v.2
    ((@Law4317.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4319 takes them (52 nodes). -/
def ordS7R325_Law4319 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4319. -/
theorem noS7R325_Law4319 : ∀ v : Magma.tup7R325,
    ¬ @Equation4319 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4319) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 4)
    (ord := ordS7R325_Law4319) (by native_decide) v.1 v.2
    ((@Law4319.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4322 takes them (136 nodes). -/
def ordS7R325_Law4322 : List (Fin 9) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- No member of the class satisfies equation 4322. -/
theorem noS7R325_Law4322 : ∀ v : Magma.tup7R325,
    ¬ @Equation4322 (Fin 7) (Magma.srch7R325 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4322) (E := S7R325.E) (tr := S7R325.tr) (z := S7R325.z)
    (st := S7R325.st) (X := S7R325.X) (envs := Magma.envsRed 7 S7R325.E 3)
    (ord := ordS7R325_Law4322) (by native_decide) v.1 v.2
    ((@Law4322.models_iff (Fin 7) (Magma.srch7R325 v)).mpr hv)

/-- No member of the class satisfies any of these `17` equations. -/
theorem srch7R325_refutes_7 :
    FamilyRefutes Magma.srch7R325 [
      4281, 4285, 4287, 4289, 4292, 4295, 4298, 4300, 4302, 4303, 4306, 4309, 4310, 4313, 4317,
      4319, 4322
    ] :=
  ⟨noS7R325_Law4281, noS7R325_Law4285, noS7R325_Law4287, noS7R325_Law4289, noS7R325_Law4292, noS7R325_Law4295, noS7R325_Law4298, noS7R325_Law4300, noS7R325_Law4302, noS7R325_Law4303, noS7R325_Law4306, noS7R325_Law4309, noS7R325_Law4310, noS7R325_Law4313, noS7R325_Law4317, noS7R325_Law4319, noS7R325_Law4322⟩
