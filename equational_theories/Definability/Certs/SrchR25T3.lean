import equational_theories.Definability.Srch_SR25

/-!
# Structural certificate targets: `Magma.srchR25` (part 4 of 7)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR25_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `15`
equations here, 3,356 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR25_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2485 takes them (139 nodes). -/
def ordSR25_Law2485 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2485. -/
theorem noSR25_Law2485 : ∀ v : Magma.tupR25,
    ¬ @Equation2485 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2496 takes them (280 nodes). -/
def ordSR25_Law2496 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2496. -/
theorem noSR25_Law2496 : ∀ v : Magma.tupR25,
    ¬ @Equation2496 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2496) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2496) (by native_decide) v.1 v.2
    ((@Law2496.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2533 takes them (193 nodes). -/
def ordSR25_Law2533 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2533. -/
theorem noSR25_Law2533 : ∀ v : Magma.tupR25,
    ¬ @Equation2533 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2533) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2533) (by native_decide) v.1 v.2
    ((@Law2533.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2653 takes them (273 nodes). -/
def ordSR25_Law2653 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2653. -/
theorem noSR25_Law2653 : ∀ v : Magma.tupR25,
    ¬ @Equation2653 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2653) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2653) (by native_decide) v.1 v.2
    ((@Law2653.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2663 takes them (169 nodes). -/
def ordSR25_Law2663 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2663. -/
theorem noSR25_Law2663 : ∀ v : Magma.tupR25,
    ¬ @Equation2663 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2663) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2663) (by native_decide) v.1 v.2
    ((@Law2663.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2699 takes them (194 nodes). -/
def ordSR25_Law2699 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2699. -/
theorem noSR25_Law2699 : ∀ v : Magma.tupR25,
    ¬ @Equation2699 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2699) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2699) (by native_decide) v.1 v.2
    ((@Law2699.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2709 takes them (217 nodes). -/
def ordSR25_Law2709 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2709. -/
theorem noSR25_Law2709 : ∀ v : Magma.tupR25,
    ¬ @Equation2709 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2709) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2709) (by native_decide) v.1 v.2
    ((@Law2709.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2736 takes them (266 nodes). -/
def ordSR25_Law2736 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2736. -/
theorem noSR25_Law2736 : ∀ v : Magma.tupR25,
    ¬ @Equation2736 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2736) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law2736) (by native_decide) v.1 v.2
    ((@Law2736.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3053 takes them (337 nodes). -/
def ordSR25_Law3053 : List (Fin 8) := [4, 5, 7, 6, 2, 0, 3, 1]

/-- No member of the class satisfies equation 3053. -/
theorem noSR25_Law3053 : ∀ v : Magma.tupR25,
    ¬ @Equation3053 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3053) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3053) (by native_decide) v.1 v.2
    ((@Law3053.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3066 takes them (356 nodes). -/
def ordSR25_Law3066 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3066. -/
theorem noSR25_Law3066 : ∀ v : Magma.tupR25,
    ¬ @Equation3066 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3066) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3066) (by native_decide) v.1 v.2
    ((@Law3066.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3079 takes them (195 nodes). -/
def ordSR25_Law3079 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3079. -/
theorem noSR25_Law3079 : ∀ v : Magma.tupR25,
    ¬ @Equation3079 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3079) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3079) (by native_decide) v.1 v.2
    ((@Law3079.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3083 takes them (137 nodes). -/
def ordSR25_Law3083 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3083. -/
theorem noSR25_Law3083 : ∀ v : Magma.tupR25,
    ¬ @Equation3083 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3083) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3083) (by native_decide) v.1 v.2
    ((@Law3083.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3094 takes them (137 nodes). -/
def ordSR25_Law3094 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3094. -/
theorem noSR25_Law3094 : ∀ v : Magma.tupR25,
    ¬ @Equation3094 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3094) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 3)
    (ord := ordSR25_Law3094) (by native_decide) v.1 v.2
    ((@Law3094.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3105 takes them (217 nodes). -/
def ordSR25_Law3105 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3105. -/
theorem noSR25_Law3105 : ∀ v : Magma.tupR25,
    ¬ @Equation3105 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3105) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3105) (by native_decide) v.1 v.2
    ((@Law3105.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3262 takes them (246 nodes). -/
def ordSR25_Law3262 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 3262. -/
theorem noSR25_Law3262 : ∀ v : Magma.tupR25,
    ¬ @Equation3262 (Fin 6) (Magma.srchR25 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3262) (E := SR25.E) (tr := SR25.tr) (z := SR25.z)
    (st := SR25.st) (X := SR25.X) (envs := Magma.envsRed 6 SR25.E 2)
    (ord := ordSR25_Law3262) (by native_decide) v.1 v.2
    ((@Law3262.models_iff (Fin 6) (Magma.srchR25 v)).mpr hv)

/-- No member of the class satisfies any of these `15` equations. -/
theorem srchR25_refutes_3 :
    FamilyRefutes Magma.srchR25 [
      2485, 2496, 2533, 2653, 2663, 2699, 2709, 2736, 3053, 3066, 3079, 3083, 3094, 3105, 3262
    ] :=
  ⟨noSR25_Law2485, noSR25_Law2496, noSR25_Law2533, noSR25_Law2653, noSR25_Law2663, noSR25_Law2699, noSR25_Law2709, noSR25_Law2736, noSR25_Law3053, noSR25_Law3066, noSR25_Law3079, noSR25_Law3083, noSR25_Law3094, noSR25_Law3105, noSR25_Law3262⟩
