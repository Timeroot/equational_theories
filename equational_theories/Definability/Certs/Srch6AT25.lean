import equational_theories.Definability.Srch_S6A

/-!
# Structural certificate targets: `Magma.srch6A` (part 26 of 52)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S6A_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `22`
equations here, 3,070 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S6A_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2648 takes them (140 nodes). -/
def ordS6A_Law2648 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2648. -/
theorem noS6A_Law2648 : ∀ v : Magma.tupS6A,
    ¬ @Equation2648 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2648) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2648) (by native_decide) v.1 v.2
    ((@Law2648.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2651 takes them (158 nodes). -/
def ordS6A_Law2651 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2651. -/
theorem noS6A_Law2651 : ∀ v : Magma.tupS6A,
    ¬ @Equation2651 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2651) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2651) (by native_decide) v.1 v.2
    ((@Law2651.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2654 takes them (266 nodes). -/
def ordS6A_Law2654 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2654. -/
theorem noS6A_Law2654 : ∀ v : Magma.tupS6A,
    ¬ @Equation2654 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2654) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2654) (by native_decide) v.1 v.2
    ((@Law2654.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2656 takes them (227 nodes). -/
def ordS6A_Law2656 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2656. -/
theorem noS6A_Law2656 : ∀ v : Magma.tupS6A,
    ¬ @Equation2656 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2656) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2656) (by native_decide) v.1 v.2
    ((@Law2656.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2657 takes them (239 nodes). -/
def ordS6A_Law2657 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2657. -/
theorem noS6A_Law2657 : ∀ v : Magma.tupS6A,
    ¬ @Equation2657 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2657) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2657) (by native_decide) v.1 v.2
    ((@Law2657.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2658 takes them (131 nodes). -/
def ordS6A_Law2658 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2658. -/
theorem noS6A_Law2658 : ∀ v : Magma.tupS6A,
    ¬ @Equation2658 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2658) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2658) (by native_decide) v.1 v.2
    ((@Law2658.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2661 takes them (97 nodes). -/
def ordS6A_Law2661 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2661. -/
theorem noS6A_Law2661 : ∀ v : Magma.tupS6A,
    ¬ @Equation2661 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2661) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2661) (by native_decide) v.1 v.2
    ((@Law2661.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2664 takes them (112 nodes). -/
def ordS6A_Law2664 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2664. -/
theorem noS6A_Law2664 : ∀ v : Magma.tupS6A,
    ¬ @Equation2664 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2664) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2664) (by native_decide) v.1 v.2
    ((@Law2664.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2666 takes them (159 nodes). -/
def ordS6A_Law2666 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2666. -/
theorem noS6A_Law2666 : ∀ v : Magma.tupS6A,
    ¬ @Equation2666 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2666) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2666) (by native_decide) v.1 v.2
    ((@Law2666.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2667 takes them (113 nodes). -/
def ordS6A_Law2667 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2667. -/
theorem noS6A_Law2667 : ∀ v : Magma.tupS6A,
    ¬ @Equation2667 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2667) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2667) (by native_decide) v.1 v.2
    ((@Law2667.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2668 takes them (47 nodes). -/
def ordS6A_Law2668 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2668. -/
theorem noS6A_Law2668 : ∀ v : Magma.tupS6A,
    ¬ @Equation2668 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2668) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2668) (by native_decide) v.1 v.2
    ((@Law2668.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2671 takes them (89 nodes). -/
def ordS6A_Law2671 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2671. -/
theorem noS6A_Law2671 : ∀ v : Magma.tupS6A,
    ¬ @Equation2671 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2671) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2671) (by native_decide) v.1 v.2
    ((@Law2671.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2674 takes them (114 nodes). -/
def ordS6A_Law2674 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2674. -/
theorem noS6A_Law2674 : ∀ v : Magma.tupS6A,
    ¬ @Equation2674 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2674) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2674) (by native_decide) v.1 v.2
    ((@Law2674.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2677 takes them (176 nodes). -/
def ordS6A_Law2677 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2677. -/
theorem noS6A_Law2677 : ∀ v : Magma.tupS6A,
    ¬ @Equation2677 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2677) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2677) (by native_decide) v.1 v.2
    ((@Law2677.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2678 takes them (66 nodes). -/
def ordS6A_Law2678 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2678. -/
theorem noS6A_Law2678 : ∀ v : Magma.tupS6A,
    ¬ @Equation2678 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2678) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2678) (by native_decide) v.1 v.2
    ((@Law2678.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2680 takes them (170 nodes). -/
def ordS6A_Law2680 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2680. -/
theorem noS6A_Law2680 : ∀ v : Magma.tupS6A,
    ¬ @Equation2680 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2680) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2680) (by native_decide) v.1 v.2
    ((@Law2680.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2681 takes them (107 nodes). -/
def ordS6A_Law2681 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2681. -/
theorem noS6A_Law2681 : ∀ v : Magma.tupS6A,
    ¬ @Equation2681 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2681) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2681) (by native_decide) v.1 v.2
    ((@Law2681.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2682 takes them (38 nodes). -/
def ordS6A_Law2682 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2682. -/
theorem noS6A_Law2682 : ∀ v : Magma.tupS6A,
    ¬ @Equation2682 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2682) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2682) (by native_decide) v.1 v.2
    ((@Law2682.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2684 takes them (190 nodes). -/
def ordS6A_Law2684 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2684. -/
theorem noS6A_Law2684 : ∀ v : Magma.tupS6A,
    ¬ @Equation2684 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2684) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2684) (by native_decide) v.1 v.2
    ((@Law2684.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2685 takes them (215 nodes). -/
def ordS6A_Law2685 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2685. -/
theorem noS6A_Law2685 : ∀ v : Magma.tupS6A,
    ¬ @Equation2685 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2685) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2685) (by native_decide) v.1 v.2
    ((@Law2685.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2686 takes them (70 nodes). -/
def ordS6A_Law2686 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2686. -/
theorem noS6A_Law2686 : ∀ v : Magma.tupS6A,
    ¬ @Equation2686 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2686) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 4)
    (ord := ordS6A_Law2686) (by native_decide) v.1 v.2
    ((@Law2686.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2689 takes them (146 nodes). -/
def ordS6A_Law2689 : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- No member of the class satisfies equation 2689. -/
theorem noS6A_Law2689 : ∀ v : Magma.tupS6A,
    ¬ @Equation2689 (Fin 6) (Magma.srch6A v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2689) (E := S6A.E) (tr := S6A.tr) (z := S6A.z)
    (st := S6A.st) (X := S6A.X) (envs := Magma.envsRed 6 S6A.E 3)
    (ord := ordS6A_Law2689) (by native_decide) v.1 v.2
    ((@Law2689.models_iff (Fin 6) (Magma.srch6A v)).mpr hv)

/-- No member of the class satisfies any of these `22` equations. -/
theorem srch6A_refutes_25 :
    FamilyRefutes Magma.srch6A [
      2648, 2651, 2654, 2656, 2657, 2658, 2661, 2664, 2666, 2667, 2668, 2671, 2674, 2677, 2678,
      2680, 2681, 2682, 2684, 2685, 2686, 2689
    ] :=
  ⟨noS6A_Law2648, noS6A_Law2651, noS6A_Law2654, noS6A_Law2656, noS6A_Law2657, noS6A_Law2658, noS6A_Law2661, noS6A_Law2664, noS6A_Law2666, noS6A_Law2667, noS6A_Law2668, noS6A_Law2671, noS6A_Law2674, noS6A_Law2677, noS6A_Law2678, noS6A_Law2680, noS6A_Law2681, noS6A_Law2682, noS6A_Law2684, noS6A_Law2685, noS6A_Law2686, noS6A_Law2689⟩
