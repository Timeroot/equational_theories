import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 9 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 2,873 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2467 takes them (966 nodes). -/
def ordS4R1_Law2467 : List (Fin 8) := [0, 2, 5, 4, 3, 1, 7, 6]

/-- No member of the class satisfies equation 2467. -/
theorem noS4R1_Law2467 : ∀ v : Magma.tup4R1,
    ¬ @Equation2467 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2467) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law2467) (by native_decide) v.1 v.2
    ((@Law2467.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2473 takes them (281 nodes). -/
def ordS4R1_Law2473 : List (Fin 8) := [2, 7, 0, 6, 5, 3, 4, 1]

/-- No member of the class satisfies equation 2473. -/
theorem noS4R1_Law2473 : ∀ v : Magma.tup4R1,
    ¬ @Equation2473 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2473) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2473) (by native_decide) v.1 v.2
    ((@Law2473.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2477 takes them (335 nodes). -/
def ordS4R1_Law2477 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2477. -/
theorem noS4R1_Law2477 : ∀ v : Magma.tup4R1,
    ¬ @Equation2477 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2477) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2477) (by native_decide) v.1 v.2
    ((@Law2477.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2481 takes them (398 nodes). -/
def ordS4R1_Law2481 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2481. -/
theorem noS4R1_Law2481 : ∀ v : Magma.tup4R1,
    ¬ @Equation2481 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2481) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2481) (by native_decide) v.1 v.2
    ((@Law2481.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2489 takes them (210 nodes). -/
def ordS4R1_Law2489 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2489. -/
theorem noS4R1_Law2489 : ∀ v : Magma.tup4R1,
    ¬ @Equation2489 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2489) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law2489) (by native_decide) v.1 v.2
    ((@Law2489.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2656 takes them (356 nodes). -/
def ordS4R1_Law2656 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2656. -/
theorem noS4R1_Law2656 : ∀ v : Magma.tup4R1,
    ¬ @Equation2656 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2656) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2656) (by native_decide) v.1 v.2
    ((@Law2656.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2676 takes them (327 nodes). -/
def ordS4R1_Law2676 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2676. -/
theorem noS4R1_Law2676 : ∀ v : Magma.tup4R1,
    ¬ @Equation2676 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2676) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2676) (by native_decide) v.1 v.2
    ((@Law2676.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch4R1_refutes_8 :
    FamilyRefutes Magma.srch4R1 [
      2467, 2473, 2477, 2481, 2489, 2656, 2676
    ] :=
  ⟨noS4R1_Law2467, noS4R1_Law2473, noS4R1_Law2477, noS4R1_Law2481, noS4R1_Law2489, noS4R1_Law2656, noS4R1_Law2676⟩
