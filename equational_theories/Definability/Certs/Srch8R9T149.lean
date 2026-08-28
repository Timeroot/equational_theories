import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 150 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `16`
equations here, 3,193 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2596 takes them (13 nodes). -/
def ordS8R9_Law2596 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2596. -/
theorem noS8R9_Law2596 : ∀ v : Magma.tup8R9,
    ¬ @Equation2596 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2596) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2596) (by native_decide) v.1 v.2
    ((@Law2596.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2605 takes them (741 nodes). -/
def ordS8R9_Law2605 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2605. -/
theorem noS8R9_Law2605 : ∀ v : Magma.tup8R9,
    ¬ @Equation2605 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2605) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2605) (by native_decide) v.1 v.2
    ((@Law2605.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2613 takes them (9 nodes). -/
def ordS8R9_Law2613 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2613. -/
theorem noS8R9_Law2613 : ∀ v : Magma.tup8R9,
    ¬ @Equation2613 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2613) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2613) (by native_decide) v.1 v.2
    ((@Law2613.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2623 takes them (741 nodes). -/
def ordS8R9_Law2623 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2623. -/
theorem noS8R9_Law2623 : ∀ v : Magma.tup8R9,
    ¬ @Equation2623 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2623) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2623) (by native_decide) v.1 v.2
    ((@Law2623.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2628 takes them (741 nodes). -/
def ordS8R9_Law2628 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2628. -/
theorem noS8R9_Law2628 : ∀ v : Magma.tup8R9,
    ¬ @Equation2628 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2628) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2628) (by native_decide) v.1 v.2
    ((@Law2628.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2633 takes them (741 nodes). -/
def ordS8R9_Law2633 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2633. -/
theorem noS8R9_Law2633 : ∀ v : Magma.tup8R9,
    ¬ @Equation2633 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2633) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2633) (by native_decide) v.1 v.2
    ((@Law2633.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2638 takes them (10 nodes). -/
def ordS8R9_Law2638 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2638. -/
theorem noS8R9_Law2638 : ∀ v : Magma.tup8R9,
    ¬ @Equation2638 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2638) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 5)
    (ord := ordS8R9_Law2638) (by native_decide) v.1 v.2
    ((@Law2638.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2645 takes them (9 nodes). -/
def ordS8R9_Law2645 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2645. -/
theorem noS8R9_Law2645 : ∀ v : Magma.tup8R9,
    ¬ @Equation2645 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2645) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 2)
    (ord := ordS8R9_Law2645) (by native_decide) v.1 v.2
    ((@Law2645.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2648 takes them (9 nodes). -/
def ordS8R9_Law2648 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2648. -/
theorem noS8R9_Law2648 : ∀ v : Magma.tup8R9,
    ¬ @Equation2648 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2648) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2648) (by native_decide) v.1 v.2
    ((@Law2648.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2651 takes them (9 nodes). -/
def ordS8R9_Law2651 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2651. -/
theorem noS8R9_Law2651 : ∀ v : Magma.tup8R9,
    ¬ @Equation2651 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2651) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2651) (by native_decide) v.1 v.2
    ((@Law2651.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2654 takes them (9 nodes). -/
def ordS8R9_Law2654 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2654. -/
theorem noS8R9_Law2654 : ∀ v : Magma.tup8R9,
    ¬ @Equation2654 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2654) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2654) (by native_decide) v.1 v.2
    ((@Law2654.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2656 takes them (103 nodes). -/
def ordS8R9_Law2656 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2656. -/
theorem noS8R9_Law2656 : ∀ v : Magma.tup8R9,
    ¬ @Equation2656 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2656) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2656) (by native_decide) v.1 v.2
    ((@Law2656.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2657 takes them (31 nodes). -/
def ordS8R9_Law2657 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2657. -/
theorem noS8R9_Law2657 : ∀ v : Magma.tup8R9,
    ¬ @Equation2657 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2657) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2657) (by native_decide) v.1 v.2
    ((@Law2657.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2658 takes them (9 nodes). -/
def ordS8R9_Law2658 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2658. -/
theorem noS8R9_Law2658 : ∀ v : Magma.tup8R9,
    ¬ @Equation2658 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2658) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2658) (by native_decide) v.1 v.2
    ((@Law2658.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2661 takes them (9 nodes). -/
def ordS8R9_Law2661 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2661. -/
theorem noS8R9_Law2661 : ∀ v : Magma.tup8R9,
    ¬ @Equation2661 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2661) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2661) (by native_decide) v.1 v.2
    ((@Law2661.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2664 takes them (9 nodes). -/
def ordS8R9_Law2664 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2664. -/
theorem noS8R9_Law2664 : ∀ v : Magma.tup8R9,
    ¬ @Equation2664 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2664) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2664) (by native_decide) v.1 v.2
    ((@Law2664.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch8R9_refutes_149 :
    FamilyRefutes Magma.srch8R9 [
      2596, 2605, 2613, 2623, 2628, 2633, 2638, 2645, 2648, 2651, 2654, 2656, 2657, 2658, 2661,
      2664
    ] :=
  ⟨noS8R9_Law2596, noS8R9_Law2605, noS8R9_Law2613, noS8R9_Law2623, noS8R9_Law2628, noS8R9_Law2633, noS8R9_Law2638, noS8R9_Law2645, noS8R9_Law2648, noS8R9_Law2651, noS8R9_Law2654, noS8R9_Law2656, noS8R9_Law2657, noS8R9_Law2658, noS8R9_Law2661, noS8R9_Law2664⟩
