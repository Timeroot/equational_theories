import equational_theories.Definability.Srch_S8R52

/-!
# Structural certificate targets: `Magma.srch8R52` (part 11 of 21)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R52_data.lean`. Each is refuted by one `Magma.searchY` over the invariant
family -- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an
instance of the equation is violated, and discards a completed table that admits an excess
permutation. `16` equations here, 3,254 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R52_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2530 takes them (306 nodes). -/
def ordS8R52_Law2530 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2530. -/
theorem noS8R52_Law2530 : ∀ v : Magma.tup8R52,
    ¬ @Equation2530 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2530) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2530) (by native_decide) v.1 v.2
    ((@Law2530.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2550 takes them (133 nodes). -/
def ordS8R52_Law2550 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2550. -/
theorem noS8R52_Law2550 : ∀ v : Magma.tup8R52,
    ¬ @Equation2550 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2550) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2550) (by native_decide) v.1 v.2
    ((@Law2550.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2567 takes them (158 nodes). -/
def ordS8R52_Law2567 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2567. -/
theorem noS8R52_Law2567 : ∀ v : Magma.tup8R52,
    ¬ @Equation2567 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2567) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2567) (by native_decide) v.1 v.2
    ((@Law2567.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2601 takes them (133 nodes). -/
def ordS8R52_Law2601 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2601. -/
theorem noS8R52_Law2601 : ∀ v : Magma.tup8R52,
    ¬ @Equation2601 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2601) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2601) (by native_decide) v.1 v.2
    ((@Law2601.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2618 takes them (133 nodes). -/
def ordS8R52_Law2618 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2618. -/
theorem noS8R52_Law2618 : ∀ v : Magma.tup8R52,
    ¬ @Equation2618 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2618) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law2618) (by native_decide) v.1 v.2
    ((@Law2618.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2679 takes them (387 nodes). -/
def ordS8R52_Law2679 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2679. -/
theorem noS8R52_Law2679 : ∀ v : Magma.tup8R52,
    ¬ @Equation2679 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2679) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2679) (by native_decide) v.1 v.2
    ((@Law2679.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2683 takes them (362 nodes). -/
def ordS8R52_Law2683 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2683. -/
theorem noS8R52_Law2683 : ∀ v : Magma.tup8R52,
    ¬ @Equation2683 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2683) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2683) (by native_decide) v.1 v.2
    ((@Law2683.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2687 takes them (265 nodes). -/
def ordS8R52_Law2687 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2687. -/
theorem noS8R52_Law2687 : ∀ v : Magma.tup8R52,
    ¬ @Equation2687 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2687) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2687) (by native_decide) v.1 v.2
    ((@Law2687.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2691 takes them (262 nodes). -/
def ordS8R52_Law2691 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2691. -/
theorem noS8R52_Law2691 : ∀ v : Magma.tup8R52,
    ¬ @Equation2691 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2691) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law2691) (by native_decide) v.1 v.2
    ((@Law2691.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2706 takes them (165 nodes). -/
def ordS8R52_Law2706 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2706. -/
theorem noS8R52_Law2706 : ∀ v : Magma.tup8R52,
    ¬ @Equation2706 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2706) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2706) (by native_decide) v.1 v.2
    ((@Law2706.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2716 takes them (133 nodes). -/
def ordS8R52_Law2716 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2716. -/
theorem noS8R52_Law2716 : ∀ v : Magma.tup8R52,
    ¬ @Equation2716 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2716) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2716) (by native_decide) v.1 v.2
    ((@Law2716.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2733 takes them (245 nodes). -/
def ordS8R52_Law2733 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2733. -/
theorem noS8R52_Law2733 : ∀ v : Magma.tup8R52,
    ¬ @Equation2733 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2733) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 2)
    (ord := ordS8R52_Law2733) (by native_decide) v.1 v.2
    ((@Law2733.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2753 takes them (133 nodes). -/
def ordS8R52_Law2753 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2753. -/
theorem noS8R52_Law2753 : ∀ v : Magma.tup8R52,
    ¬ @Equation2753 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2753) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2753) (by native_decide) v.1 v.2
    ((@Law2753.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2770 takes them (173 nodes). -/
def ordS8R52_Law2770 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2770. -/
theorem noS8R52_Law2770 : ∀ v : Magma.tup8R52,
    ¬ @Equation2770 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2770) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2770) (by native_decide) v.1 v.2
    ((@Law2770.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2787 takes them (133 nodes). -/
def ordS8R52_Law2787 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2787. -/
theorem noS8R52_Law2787 : ∀ v : Magma.tup8R52,
    ¬ @Equation2787 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2787) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 3)
    (ord := ordS8R52_Law2787) (by native_decide) v.1 v.2
    ((@Law2787.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2821 takes them (133 nodes). -/
def ordS8R52_Law2821 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2821. -/
theorem noS8R52_Law2821 : ∀ v : Magma.tup8R52,
    ¬ @Equation2821 (Fin 8) (Magma.srch8R52 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2821) (E := S8R52.E) (tr := S8R52.tr) (z := S8R52.z)
    (st := S8R52.st) (X := S8R52.X) (envs := Magma.envsRed 8 S8R52.E 4)
    (ord := ordS8R52_Law2821) (by native_decide) v.1 v.2
    ((@Law2821.models_iff (Fin 8) (Magma.srch8R52 v)).mpr hv)

/-- No member of the class satisfies any of these `16` equations. -/
theorem srch8R52_refutes_10 :
    FamilyRefutes Magma.srch8R52 [
      2530, 2550, 2567, 2601, 2618, 2679, 2683, 2687, 2691, 2706, 2716, 2733, 2753, 2770, 2787,
      2821
    ] :=
  ⟨noS8R52_Law2530, noS8R52_Law2550, noS8R52_Law2567, noS8R52_Law2601, noS8R52_Law2618, noS8R52_Law2679, noS8R52_Law2683, noS8R52_Law2687, noS8R52_Law2691, noS8R52_Law2706, noS8R52_Law2716, noS8R52_Law2733, noS8R52_Law2753, noS8R52_Law2770, noS8R52_Law2787, noS8R52_Law2821⟩
