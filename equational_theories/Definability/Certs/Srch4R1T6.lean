import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 7 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `7`
equations here, 3,651 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2045 takes them (332 nodes). -/
def ordS4R1_Law2045 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2045. -/
theorem noS4R1_Law2045 : ∀ v : Magma.tup4R1,
    ¬ @Equation2045 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2045) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2045) (by native_decide) v.1 v.2
    ((@Law2045.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2055 takes them (234 nodes). -/
def ordS4R1_Law2055 : List (Fin 8) := [4, 2, 5, 3, 6, 0, 7, 1]

/-- No member of the class satisfies equation 2055. -/
theorem noS4R1_Law2055 : ∀ v : Magma.tup4R1,
    ¬ @Equation2055 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2055) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2055) (by native_decide) v.1 v.2
    ((@Law2055.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2065 takes them (350 nodes). -/
def ordS4R1_Law2065 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2065. -/
theorem noS4R1_Law2065 : ∀ v : Magma.tup4R1,
    ¬ @Equation2065 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2065) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2065) (by native_decide) v.1 v.2
    ((@Law2065.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2182 takes them (501 nodes). -/
def ordS4R1_Law2182 : List (Fin 8) := [3, 2, 4, 5, 6, 0, 7, 1]

/-- No member of the class satisfies equation 2182. -/
theorem noS4R1_Law2182 : ∀ v : Magma.tup4R1,
    ¬ @Equation2182 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2182) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law2182) (by native_decide) v.1 v.2
    ((@Law2182.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2227 takes them (299 nodes). -/
def ordS4R1_Law2227 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2227. -/
theorem noS4R1_Law2227 : ∀ v : Magma.tup4R1,
    ¬ @Equation2227 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2227) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 4)
    (ord := ordS4R1_Law2227) (by native_decide) v.1 v.2
    ((@Law2227.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2247 takes them (681 nodes). -/
def ordS4R1_Law2247 : List (Fin 8) := [0, 2, 3, 1, 5, 4, 6, 7]

/-- No member of the class satisfies equation 2247. -/
theorem noS4R1_Law2247 : ∀ v : Magma.tup4R1,
    ¬ @Equation2247 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2247) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law2247) (by native_decide) v.1 v.2
    ((@Law2247.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2257 takes them (1254 nodes). -/
def ordS4R1_Law2257 : List (Fin 8) := [6, 0, 3, 2, 1, 4, 7, 5]

/-- No member of the class satisfies equation 2257. -/
theorem noS4R1_Law2257 : ∀ v : Magma.tup4R1,
    ¬ @Equation2257 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2257) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law2257) (by native_decide) v.1 v.2
    ((@Law2257.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `7` equations. -/
theorem srch4R1_refutes_6 :
    FamilyRefutes Magma.srch4R1 [
      2045, 2055, 2065, 2182, 2227, 2247, 2257
    ] :=
  ⟨noS4R1_Law2045, noS4R1_Law2055, noS4R1_Law2065, noS4R1_Law2182, noS4R1_Law2227, noS4R1_Law2247, noS4R1_Law2257⟩
