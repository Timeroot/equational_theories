import equational_theories.Definability.Srch_S8R2

/-!
# Structural certificate targets: `Magma.srch8R2` (part 187 of 260)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R2_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `19`
equations here, 2,267 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R2_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2490 takes them (275 nodes). -/
def ordS8R2_Law2490 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2490. -/
theorem noS8R2_Law2490 : ∀ v : Magma.tup8R2,
    ¬ @Equation2490 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2490) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2490) (by native_decide) v.1 v.2
    ((@Law2490.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2491 takes them (323 nodes). -/
def ordS8R2_Law2491 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2491. -/
theorem noS8R2_Law2491 : ∀ v : Magma.tup8R2,
    ¬ @Equation2491 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2491) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2491) (by native_decide) v.1 v.2
    ((@Law2491.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2492 takes them (71 nodes). -/
def ordS8R2_Law2492 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2492. -/
theorem noS8R2_Law2492 : ∀ v : Magma.tup8R2,
    ¬ @Equation2492 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2492) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 5)
    (ord := ordS8R2_Law2492) (by native_decide) v.1 v.2
    ((@Law2492.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2509 takes them (282 nodes). -/
def ordS8R2_Law2509 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2509. -/
theorem noS8R2_Law2509 : ∀ v : Magma.tup8R2,
    ¬ @Equation2509 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2509) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law2509) (by native_decide) v.1 v.2
    ((@Law2509.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2521 takes them (365 nodes). -/
def ordS8R2_Law2521 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2521. -/
theorem noS8R2_Law2521 : ∀ v : Magma.tup8R2,
    ¬ @Equation2521 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2521) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law2521) (by native_decide) v.1 v.2
    ((@Law2521.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2525 takes them (250 nodes). -/
def ordS8R2_Law2525 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2525. -/
theorem noS8R2_Law2525 : ∀ v : Magma.tup8R2,
    ¬ @Equation2525 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2525) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2525) (by native_decide) v.1 v.2
    ((@Law2525.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2546 takes them (17 nodes). -/
def ordS8R2_Law2546 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2546. -/
theorem noS8R2_Law2546 : ∀ v : Magma.tup8R2,
    ¬ @Equation2546 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2546) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law2546) (by native_decide) v.1 v.2
    ((@Law2546.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2562 takes them (17 nodes). -/
def ordS8R2_Law2562 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2562. -/
theorem noS8R2_Law2562 : ∀ v : Magma.tup8R2,
    ¬ @Equation2562 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2562) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2562) (by native_decide) v.1 v.2
    ((@Law2562.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2575 takes them (116 nodes). -/
def ordS8R2_Law2575 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2575. -/
theorem noS8R2_Law2575 : ∀ v : Magma.tup8R2,
    ¬ @Equation2575 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2575) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law2575) (by native_decide) v.1 v.2
    ((@Law2575.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2579 takes them (83 nodes). -/
def ordS8R2_Law2579 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2579. -/
theorem noS8R2_Law2579 : ∀ v : Magma.tup8R2,
    ¬ @Equation2579 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2579) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2579) (by native_decide) v.1 v.2
    ((@Law2579.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2596 takes them (17 nodes). -/
def ordS8R2_Law2596 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2596. -/
theorem noS8R2_Law2596 : ∀ v : Magma.tup8R2,
    ¬ @Equation2596 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2596) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2596) (by native_decide) v.1 v.2
    ((@Law2596.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2613 takes them (17 nodes). -/
def ordS8R2_Law2613 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2613. -/
theorem noS8R2_Law2613 : ∀ v : Magma.tup8R2,
    ¬ @Equation2613 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2613) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2613) (by native_decide) v.1 v.2
    ((@Law2613.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2628 takes them (18 nodes). -/
def ordS8R2_Law2628 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2628. -/
theorem noS8R2_Law2628 : ∀ v : Magma.tup8R2,
    ¬ @Equation2628 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2628) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2628) (by native_decide) v.1 v.2
    ((@Law2628.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2633 takes them (34 nodes). -/
def ordS8R2_Law2633 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2633. -/
theorem noS8R2_Law2633 : ∀ v : Magma.tup8R2,
    ¬ @Equation2633 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2633) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 4)
    (ord := ordS8R2_Law2633) (by native_decide) v.1 v.2
    ((@Law2633.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2638 takes them (18 nodes). -/
def ordS8R2_Law2638 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2638. -/
theorem noS8R2_Law2638 : ∀ v : Magma.tup8R2,
    ¬ @Equation2638 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2638) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 5)
    (ord := ordS8R2_Law2638) (by native_decide) v.1 v.2
    ((@Law2638.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2645 takes them (91 nodes). -/
def ordS8R2_Law2645 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2645. -/
theorem noS8R2_Law2645 : ∀ v : Magma.tup8R2,
    ¬ @Equation2645 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2645) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 2)
    (ord := ordS8R2_Law2645) (by native_decide) v.1 v.2
    ((@Law2645.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2648 takes them (91 nodes). -/
def ordS8R2_Law2648 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2648. -/
theorem noS8R2_Law2648 : ∀ v : Magma.tup8R2,
    ¬ @Equation2648 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2648) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law2648) (by native_decide) v.1 v.2
    ((@Law2648.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2651 takes them (91 nodes). -/
def ordS8R2_Law2651 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2651. -/
theorem noS8R2_Law2651 : ∀ v : Magma.tup8R2,
    ¬ @Equation2651 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2651) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law2651) (by native_decide) v.1 v.2
    ((@Law2651.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2654 takes them (91 nodes). -/
def ordS8R2_Law2654 : List (Fin 16) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- No member of the class satisfies equation 2654. -/
theorem noS8R2_Law2654 : ∀ v : Magma.tup8R2,
    ¬ @Equation2654 (Fin 8) (Magma.srch8R2 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2654) (E := S8R2.E) (tr := S8R2.tr) (z := S8R2.z)
    (st := S8R2.st) (X := S8R2.X) (envs := Magma.envsRed 8 S8R2.E 3)
    (ord := ordS8R2_Law2654) (by native_decide) v.1 v.2
    ((@Law2654.models_iff (Fin 8) (Magma.srch8R2 v)).mpr hv)

/-- No member of the class satisfies any of these `19` equations. -/
theorem srch8R2_refutes_186 :
    FamilyRefutes Magma.srch8R2 [
      2490, 2491, 2492, 2509, 2521, 2525, 2546, 2562, 2575, 2579, 2596, 2613, 2628, 2633, 2638,
      2645, 2648, 2651, 2654
    ] :=
  ⟨noS8R2_Law2490, noS8R2_Law2491, noS8R2_Law2492, noS8R2_Law2509, noS8R2_Law2521, noS8R2_Law2525, noS8R2_Law2546, noS8R2_Law2562, noS8R2_Law2575, noS8R2_Law2579, noS8R2_Law2596, noS8R2_Law2613, noS8R2_Law2628, noS8R2_Law2633, noS8R2_Law2638, noS8R2_Law2645, noS8R2_Law2648, noS8R2_Law2651, noS8R2_Law2654⟩
