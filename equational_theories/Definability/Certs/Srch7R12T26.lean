import equational_theories.Definability.Srch_S7R12

/-!
# Structural certificate targets: `Magma.srch7R12` (part 27 of 59)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R12_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `13` equations here, 3,365 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R12_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2476 takes them (602 nodes). -/
def ordS7R12_Law2476 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2476. -/
theorem noS7R12_Law2476 : ∀ v : Magma.tup7R12,
    ¬ @Equation2476 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2476) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2476) (by native_decide) v.1 v.2
    ((@Law2476.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2480 takes them (302 nodes). -/
def ordS7R12_Law2480 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2480. -/
theorem noS7R12_Law2480 : ∀ v : Magma.tup7R12,
    ¬ @Equation2480 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2480) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2480) (by native_decide) v.1 v.2
    ((@Law2480.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2484 takes them (315 nodes). -/
def ordS7R12_Law2484 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2484. -/
theorem noS7R12_Law2484 : ∀ v : Magma.tup7R12,
    ¬ @Equation2484 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2484) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2484) (by native_decide) v.1 v.2
    ((@Law2484.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2485 takes them (434 nodes). -/
def ordS7R12_Law2485 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2485. -/
theorem noS7R12_Law2485 : ∀ v : Magma.tup7R12,
    ¬ @Equation2485 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2485) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2485) (by native_decide) v.1 v.2
    ((@Law2485.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2488 takes them (248 nodes). -/
def ordS7R12_Law2488 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2488. -/
theorem noS7R12_Law2488 : ∀ v : Magma.tup7R12,
    ¬ @Equation2488 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2488) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2488) (by native_decide) v.1 v.2
    ((@Law2488.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2513 takes them (131 nodes). -/
def ordS7R12_Law2513 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2513. -/
theorem noS7R12_Law2513 : ∀ v : Magma.tup7R12,
    ¬ @Equation2513 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2513) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2513) (by native_decide) v.1 v.2
    ((@Law2513.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2517 takes them (131 nodes). -/
def ordS7R12_Law2517 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2517. -/
theorem noS7R12_Law2517 : ∀ v : Magma.tup7R12,
    ¬ @Equation2517 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2517) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2517) (by native_decide) v.1 v.2
    ((@Law2517.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2550 takes them (96 nodes). -/
def ordS7R12_Law2550 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2550. -/
theorem noS7R12_Law2550 : ∀ v : Magma.tup7R12,
    ¬ @Equation2550 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2550) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2550) (by native_decide) v.1 v.2
    ((@Law2550.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2554 takes them (182 nodes). -/
def ordS7R12_Law2554 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2554. -/
theorem noS7R12_Law2554 : ∀ v : Magma.tup7R12,
    ¬ @Equation2554 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2554) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2554) (by native_decide) v.1 v.2
    ((@Law2554.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2571 takes them (125 nodes). -/
def ordS7R12_Law2571 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2571. -/
theorem noS7R12_Law2571 : ∀ v : Magma.tup7R12,
    ¬ @Equation2571 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2571) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2571) (by native_decide) v.1 v.2
    ((@Law2571.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2592 takes them (159 nodes). -/
def ordS7R12_Law2592 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2592. -/
theorem noS7R12_Law2592 : ∀ v : Magma.tup7R12,
    ¬ @Equation2592 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2592) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2592) (by native_decide) v.1 v.2
    ((@Law2592.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2601 takes them (575 nodes). -/
def ordS7R12_Law2601 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2601. -/
theorem noS7R12_Law2601 : ∀ v : Magma.tup7R12,
    ¬ @Equation2601 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2601) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 3)
    (ord := ordS7R12_Law2601) (by native_decide) v.1 v.2
    ((@Law2601.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2618 takes them (65 nodes). -/
def ordS7R12_Law2618 : List (Fin 7) := [0, 1, 2, 3, 4, 5, 6]

/-- No member of the class satisfies equation 2618. -/
theorem noS7R12_Law2618 : ∀ v : Magma.tup7R12,
    ¬ @Equation2618 (Fin 7) (Magma.srch7R12 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2618) (E := S7R12.E) (tr := S7R12.tr) (z := S7R12.z)
    (st := S7R12.st) (X := S7R12.X) (envs := Magma.envsRed 7 S7R12.E 4)
    (ord := ordS7R12_Law2618) (by native_decide) v.1 v.2
    ((@Law2618.models_iff (Fin 7) (Magma.srch7R12 v)).mpr hv)

/-- No member of the class satisfies any of these `13` equations. -/
theorem srch7R12_refutes_26 :
    FamilyRefutes Magma.srch7R12 [
      2476, 2480, 2484, 2485, 2488, 2513, 2517, 2550, 2554, 2571, 2592, 2601, 2618
    ] :=
  ⟨noS7R12_Law2476, noS7R12_Law2480, noS7R12_Law2484, noS7R12_Law2485, noS7R12_Law2488, noS7R12_Law2513, noS7R12_Law2517, noS7R12_Law2550, noS7R12_Law2554, noS7R12_Law2571, noS7R12_Law2592, noS7R12_Law2601, noS7R12_Law2618⟩
