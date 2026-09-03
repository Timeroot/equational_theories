import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 4 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 3,695 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1315 takes them (1074 nodes). -/
def ordS4R1_Law1315 : List (Fin 8) := [6, 2, 7, 5, 1, 3, 4, 0]

/-- No member of the class satisfies equation 1315. -/
theorem noS4R1_Law1315 : ∀ v : Magma.tup4R1,
    ¬ @Equation1315 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1315) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law1315) (by native_decide) v.1 v.2
    ((@Law1315.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1322 takes them (812 nodes). -/
def ordS4R1_Law1322 : List (Fin 8) := [7, 0, 5, 2, 1, 6, 3, 4]

/-- No member of the class satisfies equation 1322. -/
theorem noS4R1_Law1322 : ∀ v : Magma.tup4R1,
    ¬ @Equation1322 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1322) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law1322) (by native_decide) v.1 v.2
    ((@Law1322.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1336 takes them (365 nodes). -/
def ordS4R1_Law1336 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1336. -/
theorem noS4R1_Law1336 : ∀ v : Magma.tup4R1,
    ¬ @Equation1336 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1336) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1336) (by native_decide) v.1 v.2
    ((@Law1336.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1353 takes them (369 nodes). -/
def ordS4R1_Law1353 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1353. -/
theorem noS4R1_Law1353 : ∀ v : Magma.tup4R1,
    ¬ @Equation1353 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1353) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1353) (by native_decide) v.1 v.2
    ((@Law1353.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1405 takes them (251 nodes). -/
def ordS4R1_Law1405 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1405. -/
theorem noS4R1_Law1405 : ∀ v : Magma.tup4R1,
    ¬ @Equation1405 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1405) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law1405) (by native_decide) v.1 v.2
    ((@Law1405.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1458 takes them (507 nodes). -/
def ordS4R1_Law1458 : List (Fin 8) := [6, 5, 3, 2, 7, 0, 4, 1]

/-- No member of the class satisfies equation 1458. -/
theorem noS4R1_Law1458 : ∀ v : Magma.tup4R1,
    ¬ @Equation1458 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1458) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law1458) (by native_decide) v.1 v.2
    ((@Law1458.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1460 takes them (317 nodes). -/
def ordS4R1_Law1460 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 1460. -/
theorem noS4R1_Law1460 : ∀ v : Magma.tup4R1,
    ¬ @Equation1460 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1460) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law1460) (by native_decide) v.1 v.2
    ((@Law1460.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch4R1_refutes_3 :
    FamilyRefutes Magma.srch4R1 [
      1315, 1322, 1336, 1353, 1405, 1458, 1460
    ] :=
  ⟨noS4R1_Law1315, noS4R1_Law1322, noS4R1_Law1336, noS4R1_Law1353, noS4R1_Law1405, noS4R1_Law1458, noS4R1_Law1460⟩
