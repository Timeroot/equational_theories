import equational_theories.Definability.Srch_SR7

/-!
# Structural certificate targets: `Magma.srchR7` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_SR7_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `11`
equations here, 3,295 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_SR7_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 427 takes them (613 nodes). -/
def ordSR7_Law427 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 427. -/
theorem noSR7_Law427 : ∀ v : Magma.tupR7,
    ¬ @Equation427 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law427) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 2)
    (ord := ordSR7_Law427) (by native_decide) v.1 v.2
    ((@Law427.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 837 takes them (229 nodes). -/
def ordSR7_Law837 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 837. -/
theorem noSR7_Law837 : ∀ v : Magma.tupR7,
    ¬ @Equation837 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law837) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law837) (by native_decide) v.1 v.2
    ((@Law837.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1240 takes them (162 nodes). -/
def ordSR7_Law1240 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1240. -/
theorem noSR7_Law1240 : ∀ v : Magma.tupR7,
    ¬ @Equation1240 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1240) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law1240) (by native_decide) v.1 v.2
    ((@Law1240.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1243 takes them (235 nodes). -/
def ordSR7_Law1243 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1243. -/
theorem noSR7_Law1243 : ∀ v : Magma.tupR7,
    ¬ @Equation1243 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1243) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law1243) (by native_decide) v.1 v.2
    ((@Law1243.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1250 takes them (195 nodes). -/
def ordSR7_Law1250 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1250. -/
theorem noSR7_Law1250 : ∀ v : Magma.tupR7,
    ¬ @Equation1250 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1250) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law1250) (by native_decide) v.1 v.2
    ((@Law1250.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2296 takes them (376 nodes). -/
def ordSR7_Law2296 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2296. -/
theorem noSR7_Law2296 : ∀ v : Magma.tupR7,
    ¬ @Equation2296 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2296) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law2296) (by native_decide) v.1 v.2
    ((@Law2296.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2318 takes them (307 nodes). -/
def ordSR7_Law2318 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2318. -/
theorem noSR7_Law2318 : ∀ v : Magma.tupR7,
    ¬ @Equation2318 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2318) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law2318) (by native_decide) v.1 v.2
    ((@Law2318.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2372 takes them (397 nodes). -/
def ordSR7_Law2372 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2372. -/
theorem noSR7_Law2372 : ∀ v : Magma.tupR7,
    ¬ @Equation2372 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2372) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law2372) (by native_decide) v.1 v.2
    ((@Law2372.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2778 takes them (297 nodes). -/
def ordSR7_Law2778 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2778. -/
theorem noSR7_Law2778 : ∀ v : Magma.tupR7,
    ¬ @Equation2778 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2778) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law2778) (by native_decide) v.1 v.2
    ((@Law2778.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3105 takes them (253 nodes). -/
def ordSR7_Law3105 : List (Fin 12) := [5, 10, 2, 11, 9, 0, 6, 1, 7, 4, 3, 8]

/-- No member of the class satisfies equation 3105. -/
theorem noSR7_Law3105 : ∀ v : Magma.tupR7,
    ¬ @Equation3105 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3105) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 2)
    (ord := ordSR7_Law3105) (by native_decide) v.1 v.2
    ((@Law3105.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3513 takes them (231 nodes). -/
def ordSR7_Law3513 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3513. -/
theorem noSR7_Law3513 : ∀ v : Magma.tupR7,
    ¬ @Equation3513 (Fin 6) (Magma.srchR7 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3513) (E := SR7.E) (tr := SR7.tr) (z := SR7.z)
    (st := SR7.st) (X := SR7.X) (envs := Magma.envsRed 6 SR7.E 3)
    (ord := ordSR7_Law3513) (by native_decide) v.1 v.2
    ((@Law3513.models_iff (Fin 6) (Magma.srchR7 v)).mpr hv)

/-- No member of the class satisfies any of these `11` equations. -/
theorem srchR7_refutes_0 :
    FamilyRefutes Magma.srchR7 [
      427, 837, 1240, 1243, 1250, 2296, 2318, 2372, 2778, 3105, 3513
    ] :=
  ⟨noSR7_Law427, noSR7_Law837, noSR7_Law1240, noSR7_Law1243, noSR7_Law1250, noSR7_Law2296, noSR7_Law2318, noSR7_Law2372, noSR7_Law2778, noSR7_Law3105, noSR7_Law3513⟩
