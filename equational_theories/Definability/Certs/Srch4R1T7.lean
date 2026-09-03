import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 8 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 3,395 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2260 takes them (325 nodes). -/
def ordS4R1_Law2260 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2260. -/
theorem noS4R1_Law2260 : ∀ v : Magma.tup4R1,
    ¬ @Equation2260 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2260) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2260) (by native_decide) v.1 v.2
    ((@Law2260.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2274 takes them (377 nodes). -/
def ordS4R1_Law2274 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2274. -/
theorem noS4R1_Law2274 : ∀ v : Magma.tup4R1,
    ¬ @Equation2274 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2274) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2274) (by native_decide) v.1 v.2
    ((@Law2274.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2278 takes them (274 nodes). -/
def ordS4R1_Law2278 : List (Fin 8) := [1, 7, 2, 5, 4, 0, 3, 6]

/-- No member of the class satisfies equation 2278. -/
theorem noS4R1_Law2278 : ∀ v : Magma.tup4R1,
    ¬ @Equation2278 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2278) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2278) (by native_decide) v.1 v.2
    ((@Law2278.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2286 takes them (255 nodes). -/
def ordS4R1_Law2286 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2286. -/
theorem noS4R1_Law2286 : ∀ v : Magma.tup4R1,
    ¬ @Equation2286 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2286) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law2286) (by native_decide) v.1 v.2
    ((@Law2286.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2450 takes them (637 nodes). -/
def ordS4R1_Law2450 : List (Fin 8) := [1, 6, 4, 5, 2, 3, 7, 0]

/-- No member of the class satisfies equation 2450. -/
theorem noS4R1_Law2450 : ∀ v : Magma.tup4R1,
    ¬ @Equation2450 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2450) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law2450) (by native_decide) v.1 v.2
    ((@Law2450.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2460 takes them (1194 nodes). -/
def ordS4R1_Law2460 : List (Fin 8) := [2, 4, 0, 3, 7, 6, 5, 1]

/-- No member of the class satisfies equation 2460. -/
theorem noS4R1_Law2460 : ∀ v : Magma.tup4R1,
    ¬ @Equation2460 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2460) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law2460) (by native_decide) v.1 v.2
    ((@Law2460.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2463 takes them (333 nodes). -/
def ordS4R1_Law2463 : List (Fin 8) := [4, 1, 5, 6, 0, 7, 2, 3]

/-- No member of the class satisfies equation 2463. -/
theorem noS4R1_Law2463 : ∀ v : Magma.tup4R1,
    ¬ @Equation2463 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2463) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2463) (by native_decide) v.1 v.2
    ((@Law2463.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch4R1_refutes_7 :
    FamilyRefutes Magma.srch4R1 [
      2260, 2274, 2278, 2286, 2450, 2460, 2463
    ] :=
  ⟨noS4R1_Law2260, noS4R1_Law2274, noS4R1_Law2278, noS4R1_Law2286, noS4R1_Law2450, noS4R1_Law2460, noS4R1_Law2463⟩
