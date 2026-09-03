import equational_theories.Definability.Srch_S4R1

/-!
# Structural certificate targets: `Magma.srch4R1` (part 1 of 10)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S4R1_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `10`
equations here, 3,409 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S4R1_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 124 takes them (344 nodes). -/
def ordS4R1_Law124 : List (Fin 8) := [0, 6, 2, 1, 5, 7, 3, 4]

/-- No member of the class satisfies equation 124. -/
theorem noS4R1_Law124 : ∀ v : Magma.tup4R1,
    ¬ @Equation124 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law124) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law124) (by native_decide) v.1 v.2
    ((@Law124.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 138 takes them (251 nodes). -/
def ordS4R1_Law138 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 138. -/
theorem noS4R1_Law138 : ∀ v : Magma.tup4R1,
    ¬ @Equation138 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law138) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law138) (by native_decide) v.1 v.2
    ((@Law138.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 161 takes them (317 nodes). -/
def ordS4R1_Law161 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 161. -/
theorem noS4R1_Law161 : ∀ v : Magma.tup4R1,
    ¬ @Equation161 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law161) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law161) (by native_decide) v.1 v.2
    ((@Law161.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 194 takes them (295 nodes). -/
def ordS4R1_Law194 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 194. -/
theorem noS4R1_Law194 : ∀ v : Magma.tup4R1,
    ¬ @Equation194 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law194) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law194) (by native_decide) v.1 v.2
    ((@Law194.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 206 takes them (395 nodes). -/
def ordS4R1_Law206 : List (Fin 8) := [5, 2, 4, 1, 6, 3, 7, 0]

/-- No member of the class satisfies equation 206. -/
theorem noS4R1_Law206 : ∀ v : Magma.tup4R1,
    ¬ @Equation206 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law206) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law206) (by native_decide) v.1 v.2
    ((@Law206.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 215 takes them (255 nodes). -/
def ordS4R1_Law215 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 215. -/
theorem noS4R1_Law215 : ∀ v : Magma.tup4R1,
    ¬ @Equation215 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law215) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law215) (by native_decide) v.1 v.2
    ((@Law215.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 476 takes them (574 nodes). -/
def ordS4R1_Law476 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 476. -/
theorem noS4R1_Law476 : ∀ v : Magma.tup4R1,
    ¬ @Equation476 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law476) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law476) (by native_decide) v.1 v.2
    ((@Law476.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 503 takes them (563 nodes). -/
def ordS4R1_Law503 : List (Fin 8) := [6, 7, 4, 3, 5, 2, 1, 0]

/-- No member of the class satisfies equation 503. -/
theorem noS4R1_Law503 : ∀ v : Magma.tup4R1,
    ¬ @Equation503 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law503) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 2)
    (ord := ordS4R1_Law503) (by native_decide) v.1 v.2
    ((@Law503.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 646 takes them (176 nodes). -/
def ordS4R1_Law646 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 646. -/
theorem noS4R1_Law646 : ∀ v : Magma.tup4R1,
    ¬ @Equation646 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law646) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law646) (by native_decide) v.1 v.2
    ((@Law646.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 690 takes them (239 nodes). -/
def ordS4R1_Law690 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 690. -/
theorem noS4R1_Law690 : ∀ v : Magma.tup4R1,
    ¬ @Equation690 (Fin 4) (Magma.srch4R1 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law690) (E := S4R1.E) (tr := S4R1.tr) (z := S4R1.z)
    (st := S4R1.st) (X := S4R1.X) (envs := Magma.envsRed 4 S4R1.E 3)
    (ord := ordS4R1_Law690) (by native_decide) v.1 v.2
    ((@Law690.models_iff (Fin 4) (Magma.srch4R1 v)).mpr hv)

/-- No member of the class satisfies any of these `10` equations. -/
theorem srch4R1_refutes_0 :
    FamilyRefutes Magma.srch4R1 [
      124, 138, 161, 194, 206, 215, 476, 503, 646, 690
    ] :=
  ⟨noS4R1_Law124, noS4R1_Law138, noS4R1_Law161, noS4R1_Law194, noS4R1_Law206, noS4R1_Law215, noS4R1_Law476, noS4R1_Law503, noS4R1_Law646, noS4R1_Law690⟩
