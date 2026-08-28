import equational_theories.Definability.Srch_S7R5

/-!
# Structural certificate targets: `Magma.srch7R5` (part 11 of 11)

Equations with no model whose automorphism group is exactly the group of
`Definability/Srch_S7R5_data.lean`. Each is refuted by one `Magma.searchY` over the invariant family
-- a backtracking walk that assigns one orbit at a time, kills a subtree as soon as an instance of
the equation is violated, and discards a completed table that admits an excess permutation. `5`
equations here, 3,519 search nodes between them.

This file is generated; see the module docstring of `Definability.Srch_S7R5_data`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open Law Law.MagmaLaw

/-- The orbits of the class, in the order the search for equation 2688 takes them (1140 nodes). -/
def ordS7R5_Law2688 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 2688. -/
theorem noS7R5_Law2688 : ∀ v : Magma.tup7R5,
    ¬ @Equation2688 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2688) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 3)
    (ord := ordS7R5_Law2688) (by native_decide) v.1 v.2
    ((@Law2688.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 2880 takes them (1162 nodes). -/
def ordS7R5_Law2880 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 2880. -/
theorem noS7R5_Law2880 : ∀ v : Magma.tup7R5,
    ¬ @Equation2880 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law2880) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 3)
    (ord := ordS7R5_Law2880) (by native_decide) v.1 v.2
    ((@Law2880.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3091 takes them (472 nodes). -/
def ordS7R5_Law3091 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 3091. -/
theorem noS7R5_Law3091 : ∀ v : Magma.tup7R5,
    ¬ @Equation3091 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3091) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 3)
    (ord := ordS7R5_Law3091) (by native_decide) v.1 v.2
    ((@Law3091.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 3326 takes them (309 nodes). -/
def ordS7R5_Law3326 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 3326. -/
theorem noS7R5_Law3326 : ∀ v : Magma.tup7R5,
    ¬ @Equation3326 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law3326) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 3)
    (ord := ordS7R5_Law3326) (by native_decide) v.1 v.2
    ((@Law3326.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- The orbits of the class, in the order the search for equation 4134 takes them (436 nodes). -/
def ordS7R5_Law4134 : List (Fin 13) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- No member of the class satisfies equation 4134. -/
theorem noS7R5_Law4134 : ∀ v : Magma.tup7R5,
    ¬ @Equation4134 (Fin 7) (Magma.srch7R5 v) := fun v hv ↦
  Magma.not_satisfies_of_searchY (L := Law4134) (E := S7R5.E) (tr := S7R5.tr) (z := S7R5.z)
    (st := S7R5.st) (X := S7R5.X) (envs := Magma.envsRed 7 S7R5.E 3)
    (ord := ordS7R5_Law4134) (by native_decide) v.1 v.2
    ((@Law4134.models_iff (Fin 7) (Magma.srch7R5 v)).mpr hv)

/-- No member of the class satisfies any of these `5` equations. -/
theorem srch7R5_refutes_10 :
    FamilyRefutes Magma.srch7R5 [
      2688, 2880, 3091, 3326, 4134
    ] :=
  ⟨noS7R5_Law2688, noS7R5_Law2880, noS7R5_Law3091, noS7R5_Law3326, noS7R5_Law4134⟩
