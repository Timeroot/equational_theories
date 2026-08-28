import equational_theories.Definability.Srch_S8R9

/-!
# Structural certificate targets: `Magma.srch8R9` (part 158 of 268)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S8R9_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `6`
equations here, 3,269 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S8R9_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2874 takes them (741 nodes). -/
def ordS8R9_Law2874 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2874. -/
theorem noS8R9_Law2874 : ∀ v : Magma.tup8R9,
    ¬ @Equation2874 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2874) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2874) (by native_decide) v.1 v.2
    ((@Law2874.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2877 takes them (73 nodes). -/
def ordS8R9_Law2877 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2877. -/
theorem noS8R9_Law2877 : ∀ v : Magma.tup8R9,
    ¬ @Equation2877 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2877) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2877) (by native_decide) v.1 v.2
    ((@Law2877.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2879 takes them (370 nodes). -/
def ordS8R9_Law2879 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2879. -/
theorem noS8R9_Law2879 : ∀ v : Magma.tup8R9,
    ¬ @Equation2879 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2879) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2879) (by native_decide) v.1 v.2
    ((@Law2879.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2880 takes them (741 nodes). -/
def ordS8R9_Law2880 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2880. -/
theorem noS8R9_Law2880 : ∀ v : Magma.tup8R9,
    ¬ @Equation2880 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2880) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2880) (by native_decide) v.1 v.2
    ((@Law2880.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2881 takes them (9 nodes). -/
def ordS8R9_Law2881 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2881. -/
theorem noS8R9_Law2881 : ∀ v : Magma.tup8R9,
    ¬ @Equation2881 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2881) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 4)
    (ord := ordS8R9_Law2881) (by native_decide) v.1 v.2
    ((@Law2881.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2883 takes them (1335 nodes). -/
def ordS8R9_Law2883 : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- No member of the class satisfies equation 2883. -/
theorem noS8R9_Law2883 : ∀ v : Magma.tup8R9,
    ¬ @Equation2883 (Fin 8) (Magma.srch8R9 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2883) (E := S8R9.E) (tr := S8R9.tr) (z := S8R9.z)
    (st := S8R9.st) (X := S8R9.X) (envs := Magma.envsRed 8 S8R9.E 3)
    (ord := ordS8R9_Law2883) (by native_decide) v.1 v.2
    ((@Law2883.models_iff (Fin 8) (Magma.srch8R9 v)).mpr hv)

/-- No member of the class satisfies any of these `6` equations. -/
theorem srch8R9_refutes_157 :
    FamilyRefutes Magma.srch8R9 [
      2874, 2877, 2879, 2880, 2881, 2883
    ] :=
  ⟨noS8R9_Law2874, noS8R9_Law2877, noS8R9_Law2879, noS8R9_Law2880, noS8R9_Law2881, noS8R9_Law2883⟩
