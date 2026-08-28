import equational_theories.Definability.Srch_S7R3

/-!
# Structural certificate targets: `Magma.srch7R3` (part 1 of 2)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R3_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `10`
equations here, 3,459 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R3_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 1340 takes them (183 nodes). -/
def ordS7R3_Law1340 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1340. -/
theorem noS7R3_Law1340 : ∀ v : Magma.tup7R3,
    ¬ @Equation1340 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1340) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law1340) (by native_decide) v.1 v.2
    ((@Law1340.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1374 takes them (434 nodes). -/
def ordS7R3_Law1374 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1374. -/
theorem noS7R3_Law1374 : ∀ v : Magma.tup7R3,
    ¬ @Equation1374 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1374) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law1374) (by native_decide) v.1 v.2
    ((@Law1374.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1467 takes them (405 nodes). -/
def ordS7R3_Law1467 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1467. -/
theorem noS7R3_Law1467 : ∀ v : Magma.tup7R3,
    ¬ @Equation1467 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1467) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law1467) (by native_decide) v.1 v.2
    ((@Law1467.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 1470 takes them (263 nodes). -/
def ordS7R3_Law1470 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 1470. -/
theorem noS7R3_Law1470 : ∀ v : Magma.tup7R3,
    ¬ @Equation1470 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law1470) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law1470) (by native_decide) v.1 v.2
    ((@Law1470.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2186 takes them (461 nodes). -/
def ordS7R3_Law2186 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2186. -/
theorem noS7R3_Law2186 : ∀ v : Magma.tup7R3,
    ¬ @Equation2186 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2186) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law2186) (by native_decide) v.1 v.2
    ((@Law2186.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2199 takes them (192 nodes). -/
def ordS7R3_Law2199 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2199. -/
theorem noS7R3_Law2199 : ∀ v : Magma.tup7R3,
    ¬ @Equation2199 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2199) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law2199) (by native_decide) v.1 v.2
    ((@Law2199.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2271 takes them (380 nodes). -/
def ordS7R3_Law2271 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2271. -/
theorem noS7R3_Law2271 : ∀ v : Magma.tup7R3,
    ¬ @Equation2271 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2271) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law2271) (by native_decide) v.1 v.2
    ((@Law2271.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2279 takes them (520 nodes). -/
def ordS7R3_Law2279 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 2279. -/
theorem noS7R3_Law2279 : ∀ v : Magma.tup7R3,
    ¬ @Equation2279 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2279) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law2279) (by native_decide) v.1 v.2
    ((@Law2279.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3331 takes them (336 nodes). -/
def ordS7R3_Law3331 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3331. -/
theorem noS7R3_Law3331 : ∀ v : Magma.tup7R3,
    ¬ @Equation3331 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3331) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law3331) (by native_decide) v.1 v.2
    ((@Law3331.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3534 takes them (285 nodes). -/
def ordS7R3_Law3534 : List (Fin 12) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- No member of the class satisfies equation 3534. -/
theorem noS7R3_Law3534 : ∀ v : Magma.tup7R3,
    ¬ @Equation3534 (Fin 7) (Magma.srch7R3 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3534) (E := S7R3.E) (tr := S7R3.tr) (z := S7R3.z)
    (st := S7R3.st) (X := S7R3.X) (envs := Magma.envsRed 7 S7R3.E 3)
    (ord := ordS7R3_Law3534) (by native_decide) v.1 v.2
    ((@Law3534.models_iff (Fin 7) (Magma.srch7R3 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch7R3_refutes_0 :
    FamilyRefutes Magma.srch7R3 [
      1340, 1374, 1467, 1470, 2186, 2199, 2271, 2279, 3331, 3534
    ] :=
  ⟨noS7R3_Law1340, noS7R3_Law1374, noS7R3_Law1467, noS7R3_Law1470, noS7R3_Law2186, noS7R3_Law2199, noS7R3_Law2271, noS7R3_Law2279, noS7R3_Law3331, noS7R3_Law3534⟩
